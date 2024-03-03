from transform.closure.basictype import BasicType
from transform.closure.lir_opr import LIR_Opr
from transform.closure.lir import *
from transform.closure.hir import *
from transform.closure.interval import *
from typing import Callable
from collections.abc import Mapping, MutableMapping, Sequence
from io import TextIOWrapper
from logging import getLogger
from bisect import bisect_left, bisect_right
from struct import pack, unpack

logger = getLogger(__name__)
logger.setLevel('ERROR')

class LinearScan:
    def __init__(self, f: Function):
        self.f = f
        self.blocks: list[BlockBegin] = []
        self.block_of_op_with_id: dict[int, BlockBegin] = {}

        self.intervals: dict[int, Interval] = {}
        self.new_intervals_from_allocation: list[Interval] = []
        
        self.on_phyreg_arg_vregs, self.on_stack_arg_vregs = self.get_onstack_vregs()
        self.res_on_stack_word_length = self.get_res_on_stack_word_length()
        
        self.live_in: dict[int, set[LIR_VirtualReg]] = {}
        self.live_out: dict[int, set[LIR_VirtualReg]] = {}
        
        self.move_mappings: dict[int, list[tuple[SplitParent | SplitChild, SplitChild]]] = {}
        self.move_mappings_on_block_boundary: dict[tuple[int, int], list[tuple[SplitParent | SplitChild, SplitChild] | tuple[SplitChild, SplitParent | SplitChild]]] = {}
        self.dominators: dict[int, set[int]] = {}
        self.interval_in_loop: dict[int, set[int]] = {} # interval reg_num -> set of loop indices
        self.calls: set[int] = set()
        self.max_spills: int = 0 # in words

    def append_interval(self, interval: SplitChild, /):
        # self.intervals[interval.reg_num] = interval
        self.new_intervals_from_allocation.append(interval)

    def lir_with_op_id(self, op_id: int, /):
        try:
            l = self.block_of_op_with_id[op_id].lir.lir
            i = bisect_left(l, op_id, key=lambda x: x.id)
            if i < len(l) and l[i].id == op_id:
                return l[i]
            return None
        except KeyError:
            return None

    def get_onstack_vregs(self):
        onstack_vregs: list[LIR_VirtualReg] = []
        onphyreg_vregs: list[LIR_VirtualReg] = []
        i, j = 0, 0
        for r in self.f.formal_arg_vregs:
            assert isinstance(r, LIR_VirtualReg)
            match r.basic_type:
                case BasicType.T_INT:
                    if i < 8:
                        i += 1
                        onphyreg_vregs.append(r)
                    else:
                        onstack_vregs.append(r)
                case BasicType.T_FLOAT:
                    if j < 8:
                        j += 1
                        onphyreg_vregs.append(r)
                    else:
                        onstack_vregs.append(r)
        return tuple(onphyreg_vregs), tuple(onstack_vregs)

    def get_res_on_stack_word_length(self):
        if self.f.ret_type is None:
            return 0
        bts = self.f.ret_type.to_basic_types()
        return len(bts) - min(2, bts.count(BasicType.T_FLOAT)) - min(2, bts.count(BasicType.T_INT))

    def compute_dominators(self):
        blocks = self.f.collect_all_blocks()
        in_ = {b: set[int]() for b in blocks}
        out_ = {b: set(blocks) for b in blocks}
        out_[self.f.entry.block_id] = {self.f.entry.block_id}
        del blocks[self.f.entry.block_id]
        changed = True
        while changed:
            changed = False
            for b, block in blocks.items():
                i, o = in_[b], out_[b]
                i.clear()
                if block.predesessors:
                    i |= out_[block.predesessors[0].block_id]
                for p in block.predesessors[1:]:
                    i &= out_[p.block_id]
                out_old = o.copy()
                o.clear()
                o |= i
                o.add(b)
                if out_old != o:
                    changed = True
        self.dominators = out_
        return out_
    
    def detect_loops(self):
        dominators = self.compute_dominators()
        blocks = self.f.collect_all_blocks()
        loops: dict[int, set[int]] = {} # loop header block id -> set of loop end block ids
        loop_index: dict[int, int] = {}
        loop_depth: dict[int, int] = {b: 0 for b in dominators}
        total_loops = 0
        visited = {self.f.entry.block_id}
        def dfs(b: BlockBegin, /):
            nonlocal total_loops
            for succ in b.end.sux:
                if succ.block_id not in visited:
                    visited.add(succ.block_id)
                    dfs(succ)
                elif succ.block_id in dominators[b.block_id]:
                    loops.setdefault(succ.block_id, set()).add(b.block_id)
                    if succ.block_id not in loop_index:
                        loop_index[succ.block_id] = total_loops
                        total_loops += 1
        dfs(self.f.entry)
        def dfs2(b: BlockBegin, header: BlockBegin, /):
            loop_index[b.block_id] = loop_index[header.block_id]
            loop_depth[b.block_id] += 1
            if b.block_id == header.block_id:
                return
            for p in b.predesessors:
                if p.block_id not in visited:
                    visited.add(p.block_id)
                    dfs2(p, header)

        for header, ends in loops.items():
            visited.clear()
            for end in ends:
                if end not in visited:
                    visited.add(end)
                    dfs2(blocks[end], blocks[header])

        for b in blocks.values():
            b.set_loop_info(False, False, -1, 0)
        for k, v in loop_index.items():
            blocks[k].set_loop_info(k in loops, False, v, loop_depth[k])
        for ends in loops.values():
            for end in ends:
                blocks[end].set_loop_info(False, True, loop_index[end], loop_depth[end])
                    
    def compute_incoming_forward_branches(self):
        ans = {self.f.entry.block_id: 0}
        dfn = {self.f.entry.block_id: 0}
        cnt = 0
        def dfs(b: BlockBegin):
            nonlocal cnt
            for succ in b.end.sux:
                if succ.block_id not in dfn:
                    dfn[succ.block_id] = cnt
                    ans[succ.block_id] = 1
                    cnt += 1
                    dfs(succ)
                elif dfn[succ.block_id] > dfn[b.block_id]:
                    ans[succ.block_id] += 1
        dfs(self.f.entry)
        return ans

    def compute_block_order(self):
        from heapq import heappop, heappush
        self.blocks.clear()
        worklist: list[tuple[int, int, int, int, BlockBegin]] = [(0, 0, 0, self.f.entry.block_id, self.f.entry)]
        incoming_forward_branches = self.compute_incoming_forward_branches()
        while worklist:
            _, depth, _, _, cur = heappop(worklist)
            self.blocks.append(cur)
            for i, succ in enumerate(cur.end.sux):
                incoming_forward_branches[succ.block_id] -= 1
                if incoming_forward_branches[succ.block_id] == 0:
                    heappush(worklist, (-succ.loop_depth, depth - 1, i, succ.block_id, succ))
        assert len(self.blocks) == len(incoming_forward_branches)
        return self.blocks
    
    def number_operations(self):
        assert all(b.lir.is_finished for b in self.blocks)
        next_id = 0
        for b in self.blocks:
            for op in b.lir.lir:
                op.id = next_id
                self.block_of_op_with_id[next_id] = self.block_of_op_with_id[next_id + 1] = b
                next_id += 2
    
    def compute_local_live_sets(self):
        live_gen: dict[int, set[LIR_VirtualReg]] = {}
        live_kill: dict[int, set[LIR_VirtualReg]] = {}
        for b in self.blocks:
            assert isinstance(b.lir.lir[0], LIR_OpLabel) and isinstance(b.lir.lir[-1], (LIR_OpReturn, LIR_OpBranCond, LIR_OpGoto))
            assert len(b.lir.patch_moves) == 0
            live_gen[b.block_id] = set()
            live_kill[b.block_id] = set()

            if b.loop_index < 0:
                for op in b.lir.lir:
                    if op.is_call:
                        self.calls.add(op.id)
                    for opr in op.input_oprs():
                        if isinstance(opr, LIR_VirtualReg) and opr not in live_kill[b.block_id]:
                            live_gen[b.block_id].add(opr)
                    for opr in op.tmp_oprs():
                        if isinstance(opr, LIR_VirtualReg): live_kill[b.block_id].add(opr)
                    for opr in op.output_oprs():
                        if isinstance(opr, LIR_VirtualReg): live_kill[b.block_id].add(opr)
            else:
                for op in b.lir.lir:
                    if op.is_call:
                        self.calls.add(op.id)
                    for opr in op.input_oprs():
                        if isinstance(opr, LIR_VirtualReg) and opr not in live_kill[b.block_id]:
                            live_gen[b.block_id].add(opr)
                            if opr.reg_num not in self.interval_in_loop: self.interval_in_loop[opr.reg_num] = set()
                            self.interval_in_loop[opr.reg_num].add(b.loop_index)
                    for opr in op.tmp_oprs():
                        if isinstance(opr, LIR_VirtualReg):
                            live_kill[b.block_id].add(opr)
                            if opr.reg_num not in self.interval_in_loop: self.interval_in_loop[opr.reg_num] = set()
                            self.interval_in_loop[opr.reg_num].add(b.loop_index)
                    for opr in op.output_oprs():
                        if isinstance(opr, LIR_VirtualReg):
                            live_kill[b.block_id].add(opr)
                            if opr.reg_num not in self.interval_in_loop: self.interval_in_loop[opr.reg_num] = set()
                            self.interval_in_loop[opr.reg_num].add(b.loop_index)
            
        return live_gen, live_kill

    def compute_global_live_sets(self):
        live_out = {b.block_id: set[LIR_VirtualReg]() for b in self.blocks}
        live_in = {b.block_id: set[LIR_VirtualReg]() for b in self.blocks}
        live_gen, live_kill = self.compute_local_live_sets()
        tmp_live_out = set[LIR_VirtualReg]()
        changed = True
        while changed:
            changed = False
            for b in reversed(self.blocks):
                tmp_live_out.clear()
                for succ in b.end.sux:
                    tmp_live_out |= live_in[succ.block_id]
                tmp_live_in = live_gen[b.block_id] | (tmp_live_out - live_kill[b.block_id])
                if tmp_live_in != live_in[b.block_id]:
                    live_in[b.block_id].clear(); live_in[b.block_id].update(tmp_live_in)
                    changed = True
                if tmp_live_out != live_out[b.block_id]:
                    live_out[b.block_id].clear(); live_out[b.block_id].update(tmp_live_out)
                    changed = True
                    
        assert not live_in[self.f.entry.block_id]
        return live_in, live_out

    def create_interval(self, reg_num: int, type: BasicType, /):
        assert 0 <= reg_num and reg_num not in self.intervals
        self.intervals[reg_num] = interval = SplitParent(reg_num, type)
        if reg_num < LIR_Opr.n_phyregs:
            interval.assign_reg(reg_num)
        return interval
    
    def build_intervals(self):
        live_in, live_out = self.compute_global_live_sets()
        self.live_in, self.live_out = live_in, live_out
        caller_saved_regs = (*LIR_CpuReg.caller_saveds(), *LIR_FloatReg.caller_saveds())
        for b in reversed(self.blocks):
            block_from = b.lir.lir[0].id
            block_to = b.lir.lir[-1].id

            for opr in live_out[b.block_id]:
                self.add_use(opr.reg_num, block_from, block_to + 2, None, opr.basic_type)
                if b.is_loop_end and b.loop_index != -1 and opr.reg_num in self.interval_in_loop:
                    self.intervals[opr.reg_num].add_use_pos(block_to + 1, IntervalUseKind.loopEndMarker)
                
            for i, op in enumerate(reversed(b.lir.lir)):
                if op.is_call:
                    # add fixed intervals for caller-saved registers
                    for r in caller_saved_regs:
                        self.add_temp(r.reg_num, op.id, None, r.basic_type)

                for opr in op.output_oprs():
                    kind = None if isinstance(op, LIR_OpRestore) else IntervalUseKind.mustHaveRegister
                    self.add_def(opr.reg_num, op.id, kind, opr.basic_type)
                
                for opr in op.tmp_oprs():
                    self.add_temp(opr.reg_num, op.id, IntervalUseKind.mustHaveRegister, opr.basic_type)

                for opr in op.input_oprs():
                    self.add_use(opr.reg_num, block_from, op.id, self.use_kind_of_input_oprand(op, opr), opr.basic_type)

                self.add_register_hints(op)
        self.handle_method_arguments()
        for i in range(LIR_Opr.n_phyregs):
            if (interval:=self.intervals.get(i)) is not None:
                interval.add_range(0, 1)

    def add_use(self, reg_num: int, from_: int, to: int, use_kind: IntervalUseKind | None, type: BasicType, /):
        interval = self.intervals.get(reg_num)
        if interval is None: interval = self.create_interval(reg_num, type)
        assert interval.reg_num == reg_num, "wrong interval"
        interval.add_range(from_, to)
        interval.add_use_pos(to, use_kind)
    
    def add_temp(self, reg_num: int, temp_pos: int, use_kind: IntervalUseKind | None, type: BasicType, /):
        interval = self.intervals.get(reg_num)
        if interval is None: interval = self.create_interval(reg_num, type)
        assert interval.reg_num == reg_num, "wrong interval"
        interval.add_range(temp_pos, temp_pos + 1)
        interval.add_use_pos(temp_pos, use_kind)
    
    def add_def(self, reg_num: int, def_pos: int, use_kind: IntervalUseKind | None, type: BasicType, /):
        interval = self.intervals.get(reg_num)
        if interval is not None:
            assert interval.reg_num == reg_num, "wrong interval"
            r = interval.first_range
            if r.from_ <= def_pos:
                # Update the starting point (when a range is first created for a use, its
                # start is the beginning of the current block until a def is encountered.)
                r.from_ = def_pos
                interval.add_use_pos(def_pos, use_kind)
            else:
                # Dead value - make vacuous interval
                # also add use_kind for dead intervals
                interval.add_range(def_pos, def_pos + 1)
                interval.add_use_pos(def_pos, use_kind)
                logger.warning(f"{self.f.name}: dead def: reg {reg_num}, def_pos {def_pos}, use_kind {use_kind}")
        else:
            # Dead value - make vacuous interval
            # also add use_kind for dead intervals
            interval = self.create_interval(reg_num, type)
            interval.add_range(def_pos, def_pos + 1)
            interval.add_use_pos(def_pos, use_kind)
            logger.warning(f"{self.f.name}: dead def: reg {reg_num}, def_pos {def_pos}, use_kind {use_kind}")
        
        assert isinstance(interval, SplitParent)
        self.change_spill_definition_pos(interval, def_pos)

    def change_spill_definition_pos(self, interval: SplitParent, def_pos: int, /):
        match interval.spill_state:
            case IntervalSpillState.noDefinitionFound:
                interval.spill_state = IntervalSpillState.oneDefinitionFound
                interval.spill_definition_pos = def_pos

            case IntervalSpillState.oneDefinitionFound:
                assert def_pos <= interval.spill_definition_pos, 'positions are processed in reverse order when intervals are created'
                if def_pos < interval.spill_definition_pos - 2:
                    interval.spill_state = IntervalSpillState.noOptimization
                else:
                    assert self.block_of_op_with_id[def_pos].block_id == self.block_of_op_with_id[interval.spill_definition_pos].block_id, 'block must be equal'
            
            case IntervalSpillState.noOptimization:
                ...
            
            case _:
                assert False, f"{interval.spill_state} not allowed at this time"
    
    def use_kind_of_input_oprand(self, op: LIR_Op, opr: LIR_Reg, /) -> IntervalUseKind:
        if isinstance(op, LIR_OpMove):
            res = op.result
            assert res is not None
            if is_lir_reg(res) and is_lir_reg(opr):
                return IntervalUseKind.shouldHaveRegister
        return IntervalUseKind.mustHaveRegister

    def handle_method_arguments(self):
        # a, fa = 0, 0
        # for i, opr in enumerate(self.on_phyreg_arg_vregs):
        #     self.add_def(opr.reg_num, 0, IntervalUseKind.mustHaveRegister, opr.basic_type)
        #     if (interval:=self.intervals.get(opr.reg_num)) is not None:
        #         assert isinstance(interval, SplitParent)
        #         if opr.basic_type is BasicType.T_INT:
        #             hint = self.intervals[LIR_CpuReg(f'a{a}').reg_num]
        #             assert isinstance(hint, SplitParent)
        #             interval.set_register_hint(hint); a += 1
        #         else:
        #             hint = self.intervals[LIR_FloatReg(f'fa{fa}').reg_num]
        #             assert isinstance(hint, SplitParent)
        #             interval.set_register_hint(hint); fa += 1
        # assert a <= 8 and fa <= 8
        for i, opr in enumerate(self.on_stack_arg_vregs):
            stackslot = LIR_Opr.n_phyregs + len(self.on_stack_arg_vregs) - i - 1
            if (interval:=self.intervals.get(opr.reg_num)) is not None:
                assert isinstance(interval, SplitParent)
                interval.canonical_spill_slot = stackslot
                interval.assign_reg(stackslot)
                interval.spill_state = IntervalSpillState.startInMemory

    def add_register_hints(self, op: LIR_Op, /):
        if isinstance(op, (LIR_OpMove, LIR_OpConvert)) and is_lir_reg(op.result) and is_lir_reg(op.opr):
            from_ = self.intervals.get(op.opr.reg_num)
            to = self.intervals.get(op.result.reg_num)
            if from_ is not None and to is not None:
                assert isinstance(to, SplitParent) and isinstance(from_, SplitParent)
                to.set_register_hint(from_)

    @staticmethod
    def is_precolored_cpu_interval(interval: Interval, /):
        return 0 <= interval.reg_num < LIR_Opr.n_cpu_regs
    @staticmethod
    def is_precolored_float_interval(interval: Interval, /):
        return LIR_Opr.n_cpu_regs <= interval.reg_num < LIR_Opr.n_phyregs
    
    @staticmethod
    def is_virtual_cpu_interval(interval: Interval, /):
        return LIR_Opr.vreg_base <= interval.reg_num and interval.type is BasicType.T_INT
    
    @staticmethod
    def is_virtual_float_interval(interval: Interval, /):
        return LIR_Opr.vreg_base <= interval.reg_num and interval.type is BasicType.T_FLOAT
    
    def sort_intervals_before_allocation(self):
        self.intervals = dict(sorted(self.intervals.items(), key=lambda x: x[1].from_))
    def sort_intervals_after_allocation(self):
        self.intervals = dict(sorted(self.intervals.items(), key=lambda x: x[1].from_))

    def allocate_registers(self):
        unhandled = list(self.intervals.values())
        handled: dict[int, Interval] = {}
        active: dict[int, Interval] = {}
        inactive: dict[int, Interval] = {}

        def append_to_unhandled(it: SplitChild):
            assert position <= it.from_
            i = 0
            while i < len(unhandled):
                if unhandled[i].from_ < it.from_: i += 1
                elif unhandled[i].from_ == it.from_:
                    x1 = unhandled[i].first_usage(IntervalUseKind.shouldHaveRegister)
                    x2 = it.first_usage(IntervalUseKind.shouldHaveRegister)
                    if x1 < x2: i += 1
                    else: break
                else: break
            unhandled.insert(i, it)
        
        def append_to_handled(it: Interval):
            assert it.reg_num not in handled
            handled[it.reg_num] = it
        
        while unhandled:
            current = unhandled.pop(0)
            position = current.from_

            active_to_handled: list[Interval] = []
            active_to_inactivate: list[Interval] = []

            for it in active.values():
                if it.to <= position:
                    active_to_handled.append(it)
                else:
                    i = bisect_right(it.ranges, position, key=lambda x: x.to)
                    assert position < it.ranges[i].to
                    if position < it.ranges[i].from_:
                        active_to_inactivate.append(it)

            for it in active_to_handled:
                active.pop(it.reg_num)
                handled[it.reg_num] = it
            for it in active_to_inactivate:
                active.pop(it.reg_num)
                inactive[it.reg_num] = it

            inactive_to_handled: list[Interval] = []
            inactive_to_active: list[Interval] = []

            
            for it in inactive.values():
                if it.to <= position:
                    inactive_to_handled.append(it)
                else:
                    i = bisect_right(it.ranges, position, key=lambda x: x.to)
                    assert position < it.ranges[i].to
                    if it.ranges[i].from_ <= position:
                        inactive_to_active.append(it)

            for it in inactive_to_handled:
                inactive.pop(it.reg_num)
                handled[it.reg_num] = it
            for it in inactive_to_active:
                inactive.pop(it.reg_num)
                active[it.reg_num] = it

            if self.activate_current(position, current, active, inactive, append_to_unhandled, append_to_handled):
                assert 0 <= current.assigned_reg < LIR_Opr.n_phyregs
                assert current.reg_num not in active
                active[current.reg_num] = current
            else:
                assert current.assigned_reg >= LIR_Opr.n_phyregs
                assert current.reg_num not in handled
                handled[current.reg_num] = current
            
        assert len(unhandled) == 0
        assert len(handled) + len(inactive) + len(active) == len(self.intervals) + len(self.new_intervals_from_allocation)
        self.intervals.update({it.reg_num: it for it in self.new_intervals_from_allocation})

    def activate_current(self, position: int, current: Interval, active: MutableMapping[int, Interval], inactive: MutableMapping[int, Interval], append_to_unhandled: Callable[[SplitChild], None], append_to_handled: Callable[[Interval], None], /):
        res = True
        assert position == current.from_
        if current.assigned_reg >= LIR_Opr.n_phyregs:
            logger.debug(f"  interval {current.reg_num} has spill slot assigned, split it before first use")
            self.split_stack_interval(position, current, append_to_unhandled)
            res = False
        elif current.assigned_reg == -1:
            logger.debug(f"  interval {current.reg_num} has no register assigned, try to allocate one")
            # self.combine_spilled_intervals(current, active, inactive)
            def combine_spilled_intervals(it: SplitParent):
                if (register_hint := it.register_hint(False)) is None:
                    return
                if it.spill_state is not IntervalSpillState.noOptimization or register_hint.spill_state is not IntervalSpillState.noOptimization:
                    # combining the stack slots for intervals where spill move optimization is applied
                    # is not benefitial and would cause problems
                    return
                begin_pos, end_pos = it.from_, it.to
                if end_pos > self.blocks[-1].lir.lir[-1].id or begin_pos & 1 != 0 or end_pos & 1 != 0:
                    # safety check that lir_with_op_id is allowed
                    return
                if not isinstance(self.lir_with_op_id(begin_pos), LIR_OpMove) or not isinstance(self.lir_with_op_id(end_pos - 1), LIR_OpMove):
                    return 
                begin_hint = register_hint.split_child_at_op_id(begin_pos, 'input')
                end_hint = register_hint.split_child_at_op_id(end_pos, 'output')
                if begin_hint is end_hint or begin_hint.to != begin_pos or end_hint.from_ != end_pos:
                    # register_hint must be split, otherwise the re-writing of use positions does not work
                    return
                assert begin_hint.assigned_reg != -1 and end_hint.assigned_reg == -1
                assert it.first_usage(IntervalUseKind.mustHaveRegister) == begin_pos, "must have use position at begin of interval because of move"
                assert end_hint.first_usage(IntervalUseKind.mustHaveRegister) == end_pos, "must have use position at end of interval because of move"
                if begin_hint.assigned_reg < LIR_Opr.n_phyregs:
                    # register_hint is not spilled at begin_pos, so it would not be benefitial to immediately spill `it`
                    return
                if it.intersects_any_children_of(register_hint):
                    # An overlap of two intervals with the same spill slot could result in a situation 
                    # where both intervals are spilled at the same time to the same stack location, which is not correct.
                    return
                logger.debug(f"    combining spill slots of intervals {it.reg_num} and {register_hint.reg_num}")
                it.canonical_spill_slot = register_hint.canonical_spill_slot
                it.use_positions.pop()
                end_hint.use_positions.pop()
            
            if isinstance(current, SplitParent):
                combine_spilled_intervals(current)

            if not self.try_allocate_free_reg(current, active, inactive, append_to_unhandled):
                self.allocate_blocked_reg(position, current, active, inactive, append_to_unhandled, append_to_handled)
            if current.assigned_reg >= LIR_Opr.n_phyregs:
                res = False
        
        if current.insert_move_when_activated:
            assert isinstance(current, SplitChild)
            assert current.current_split_child.reg_num != current.reg_num
            self.insert_move(position, current.current_split_child, current)
        
        if isinstance(current, SplitChild):
            current.make_current_split_child()
        
        return res

    def try_allocate_free_reg(self, current: Interval, active: Mapping[int, Interval], inactive: Mapping[int, Interval], /, append_to_unhandled: Callable[[SplitChild], None]):
        assert current.assigned_reg == -1
        free_pos: dict[int, int] = {i: 2**30 for i in range(LIR_Opr.n_phyregs)}
        
        match current.type:
            case BasicType.T_INT:
                del free_pos[0], free_pos[1], free_pos[2], free_pos[3],free_pos[4]
                for i in range(LIR_Opr.n_cpu_regs, LIR_Opr.n_phyregs):
                    del free_pos[i]
            case BasicType.T_FLOAT:
                for i in range(LIR_Opr.n_cpu_regs):
                    del free_pos[i]

        for it in active.values():
            free_pos[it.assigned_reg] = 0

        for it in inactive.values():
            intersect_pos = it.intersects(current)
            if intersect_pos is not None and it.assigned_reg in free_pos:
                free_pos[it.assigned_reg] = min(free_pos[it.assigned_reg], intersect_pos)

        register_hint = current.register_hint(True)
        hint_reg = register_hint.assigned_reg if register_hint is not None else None
        assert hint_reg is None or 0 <= hint_reg < LIR_Opr.n_phyregs
        reg, need_split = self.find_free_reg(free_pos, current.from_ + 1, current.to, hint_reg)
        if reg is None:
            return False
        current.assign_reg(reg)
        if need_split:
            self.split_when_partial_register_available(current, free_pos[reg], append_to_unhandled)
        return True

    def find_free_reg(self, free_pos: Mapping[int, int], reg_needed_until: int, interval_to: int, hint_reg: int | None):
        min_full_reg = None
        max_partial_reg = None
        for i, pos in free_pos.items():
            if pos >= interval_to:
                if min_full_reg is None or i == hint_reg or (pos < free_pos[min_full_reg] and min_full_reg != hint_reg):
                    min_full_reg = i
            elif pos > reg_needed_until:
                if max_partial_reg is None or i == hint_reg or (pos > free_pos[max_partial_reg] and max_partial_reg != hint_reg):
                    max_partial_reg = i
        if min_full_reg is not None:
            return min_full_reg, False
        if max_partial_reg is not None:
            return max_partial_reg, True
        return None, None

    def split_when_partial_register_available(self, it: Interval, register_available_until: int, /, append_to_unhandled: Callable[[SplitChild], None]):
        min_split_pos = max(it.previous_usage(IntervalUseKind.shouldHaveRegister, register_available_until), it.from_ + 1)
        max_split_pos = register_available_until
        self.split_before_usage(it, min_split_pos, max_split_pos, append_to_unhandled)
    
    def split_before_usage(self, it: Interval, min_split_pos: int, max_split_pos: int, /, append_to_unhandled: Callable[[SplitChild], None]):
        assert it.from_ < min_split_pos <= max_split_pos <= it.to
        optimal_split_pos = self.find_optimal_split_pos(it, min_split_pos, max_split_pos, True)
        assert min_split_pos <= optimal_split_pos <= max_split_pos
        assert it.from_ < optimal_split_pos <= it.to

        if optimal_split_pos == it.to and it.next_usage(IntervalUseKind.mustHaveRegister, min_split_pos) == Range.MAX:
            logger.debug(f"    no split necessary because optimal split position is at the end of the interval")
            return
        
        move_necessary = not self.is_block_begin(optimal_split_pos) and not it.has_hole_between(optimal_split_pos - 1, optimal_split_pos)

        if not self.is_block_begin(optimal_split_pos):
            optimal_split_pos = (optimal_split_pos - 1) | 1
        
        split_part = it.split(optimal_split_pos)
        self.append_interval(split_part)
        if move_necessary:
            split_part.set_insert_move_when_activated()
        
        append_to_unhandled(split_part)
        
    
    def split_stack_interval(self, position: int, it: Interval, /, append_to_unhandled: Callable[[SplitChild], None]):
        min_split_pos = position + 1
        max_split_pos = min(it.first_usage(IntervalUseKind.shouldHaveRegister), it.to)
        self.split_before_usage(it, min_split_pos, max_split_pos, append_to_unhandled)

    def is_block_begin(self, op_id: int, /):
        return op_id == 0 or self.block_of_op_with_id[op_id] != self.block_of_op_with_id[op_id - 1]
    
    def find_optimal_split_pos(self, it: Interval, min_split_pos: int, max_split_pos: int, /, do_loop_optimization: bool):
        optimal_split_pos = None
        if min_split_pos == max_split_pos:
            optimal_split_pos = min_split_pos
        else:
            assert 0 < min_split_pos < max_split_pos
            min_block = self.block_of_op_with_id[min_split_pos - 1]
            max_block = self.block_of_op_with_id[max_split_pos - 1]
            assert self.blocks.index(min_block) <= self.blocks.index(max_block)
            if min_block == max_block:
                # split position cannot be moved to block boundary, so split as late as possible
                optimal_split_pos = max_split_pos
            elif it.has_hole_between(max_split_pos - 1, max_split_pos) and not self.is_block_begin(max_split_pos):
                optimal_split_pos = max_split_pos
            else:
                if do_loop_optimization:
                    loop_end_pos = it.next_usage_exact(IntervalUseKind.loopEndMarker, min_block.lir.lir[-1].id + 2)
                    logger.debug(f"    loop_end_pos: {loop_end_pos}, it: {it.reg_num}, from: {min_block.lir.lir[-1].id + 2}")
                    assert min_split_pos < loop_end_pos
                    if loop_end_pos < max_split_pos:
                        # loop-end marker found between min- and max-position
                        # if it is not the end marker for the same loop as the min-position, then move the max-position to this loop block.
                        # Desired result: uses tagged as shouldHaveRegister inside a loop cause a reloading
                        # of the interval (normally, only mustHaveRegister causes a reloading)
                        loop_block = self.block_of_op_with_id[loop_end_pos]
                        optimal_split_pos = self.find_optimal_split_pos_in_block(min_block, loop_block, loop_block.lir.lir[-1].id + 2)
                        if optimal_split_pos == loop_block.lir.lir[-1].id + 2:
                            optimal_split_pos = None
                            logger.debug("    loop optimization not necessary")
                        else:
                            logger.debug("    loop optimization successful")

                if optimal_split_pos is None:
                    optimal_split_pos = self.find_optimal_split_pos_in_block(min_block, max_block, max_split_pos)
        return optimal_split_pos

    def find_optimal_split_pos_in_block(self, min_block: BlockBegin, max_block: BlockBegin, max_split_pos: int, /):
        from_block_nr = self.blocks.index(min_block)
        to_block_nr = self.blocks.index(max_block)
        assert from_block_nr < to_block_nr
        optimal_split_pos = max_block.lir.lir[-1].id + 2
        if optimal_split_pos > max_split_pos: optimal_split_pos = max_block.lir.lir[0].id
        argmin = min(reversed(range(from_block_nr, to_block_nr + 1)), key=lambda x: self.blocks[x].loop_depth)
        if argmin != to_block_nr: optimal_split_pos = self.blocks[argmin].lir.lir[-1].id + 2
        return optimal_split_pos
    
    def allocate_blocked_reg(self, position: int, current: Interval, active: MutableMapping[int, Interval], inactive: MutableMapping[int, Interval], /, append_to_unhandled: Callable[[SplitChild], None], append_to_handled: Callable[[Interval], None]):
        use_pos = {i: Range.MAX for i in range(LIR_Opr.n_phyregs)}
        block_pos = {i: Range.MAX for i in range(LIR_Opr.n_phyregs)}
        spill_intervals = {i: list[Interval]() for i in range(LIR_Opr.n_phyregs)}
        
        for it in active.values():
            if not it.is_fixed:
                a = min(it.next_usage(IntervalUseKind.loopEndMarker, position), it.to)
                use_pos[it.assigned_reg] = min(use_pos[it.assigned_reg], a)
                spill_intervals[it.assigned_reg].append(it)
            else:
                use_pos[it.assigned_reg] = 0
        
        for it in inactive.values():
            if (next:=it.intersects(current)) is not None:
                if not it.is_fixed:
                    a = min(it.next_usage(IntervalUseKind.loopEndMarker, position), it.to)
                    use_pos[it.assigned_reg] = min(use_pos[it.assigned_reg], a)
                    spill_intervals[it.assigned_reg].append(it)
                else:
                    block_pos[it.assigned_reg] = min(block_pos[it.assigned_reg], next)
                    use_pos[it.assigned_reg] = min(use_pos[it.assigned_reg], next)
                    # if current.to >
        
        reg_need_until = min(current.first_usage(IntervalUseKind.mustHaveRegister), current.from_ + 1)
        assert 0 < reg_need_until < Range.MAX, "interval has no use"
        _split_pos, _use_pos = 0, 0
        assert current.assigned_reg < 0
        reg, need_split = self.find_locked_reg(current.type, use_pos, block_pos, reg_need_until, current.to, current.assigned_reg)
        if reg is not None:
            _use_pos = use_pos[reg]
            _split_pos = block_pos[reg]

        if reg is None or _use_pos <= current.first_usage(IntervalUseKind.mustHaveRegister):
            # the first use of current is later than the spilling position => spill current
            assert current.first_usage(IntervalUseKind.mustHaveRegister) > current.from_ + 1, "no register found"
            assert current not in active and current not in inactive
            active[current.reg_num] = current
            self.spilt_and_spill_interval(position, current, active, inactive, append_to_unhandled, append_to_handled)
            del active[current.reg_num]
        else:
            assert reg is not None and 0 < _split_pos
            assert not need_split or _split_pos > current.from_

            current.assign_reg(reg)
            if need_split:
                self.split_when_partial_register_available(current, _split_pos, append_to_unhandled)

            self.split_and_spill_intersecting_intervals(position, active, inactive, spill_intervals[reg], append_to_unhandled, append_to_handled)


    def find_locked_reg(self, type: BasicType, use_pos: Mapping[int, int], block_pos: Mapping[int, int], reg_need_until: int, interval_to: int, ignore_reg: int, /):
        max_reg = None
        r = range(5, LIR_Opr.n_cpu_regs) if type is BasicType.T_INT else range(LIR_Opr.n_cpu_regs, LIR_Opr.n_phyregs)
        for i in r:
            if i == ignore_reg: continue
            if use_pos[i] > reg_need_until:
                if max_reg is None or use_pos[i] > use_pos[max_reg]:
                    max_reg = i
        if max_reg is not None and block_pos[max_reg] <= interval_to:
            return max_reg, True
        return max_reg, False

    def spilt_and_spill_interval(self, position: int, it: Interval, active: Mapping[int, Interval], inactive: Mapping[int, Interval], /, append_to_unhandled: Callable[[SplitChild], None], append_to_handled: Callable[[Interval], None]):
        assert int(it.reg_num in active) + int(it.reg_num in inactive) == 1
        if it.reg_num in inactive:
            assert it.has_hole_between(position - 1, position + 1)
            self.split_before_usage(it, position + 1, position + 1, append_to_unhandled)
        else:
            min_split_pos = position + 1
            max_split_pos = min(it.next_usage(IntervalUseKind.mustHaveRegister, min_split_pos), it.to)
            self.split_before_usage(it, min_split_pos, max_split_pos, append_to_unhandled)
            assert it.next_usage(IntervalUseKind.mustHaveRegister, position) == Range.MAX
            self.split_for_spilling(it, position, active, append_to_handled)
        
    def split_for_spilling(self, it: Interval, position: int, active: Mapping[int, Interval], /, append_to_handled: Callable[[SplitChild], None]):
        max_split_pos = position
        min_split_pos = max(it.previous_usage(IntervalUseKind.shouldHaveRegister, max_split_pos) + 1, it.from_)
        assert it.reg_num in active, "why spill an inactive interval?"
        assert it.from_ <= min_split_pos <= max_split_pos < it.to
        assert position < it.to, "interval must not end before current position"

        if min_split_pos == it.from_:
            # the whole interval is never used => spill it entirely to memory
            assert position < it.first_usage(IntervalUseKind.shouldHaveRegister)
            self.assign_spill_slot(it)
            self.change_spill_state(it, min_split_pos)

            parent = it
            while isinstance(parent, SplitChild):
                parent = parent.split_parent.split_child_before_op_id(parent.from_)
                assert parent.assigned_reg != -1
                if parent.assigned_reg < LIR_Opr.n_phyregs:
                    if parent.first_usage(IntervalUseKind.shouldHaveRegister) == Range.MAX:
                        # parent is never used, so kick it out of its assigned register
                        logger.debug(f"  kicking out interval {parent.reg_num} out of its register because it is never used")
                        self.assign_spill_slot(parent)        
                    else:
                        # do not go further back because the register is actually used by the interval
                        break
        else:
            # search optimal split pos, split interval and spill only the right hand part
            optimal_split_pos = self.find_optimal_split_pos(it, min_split_pos, max_split_pos, False)
            assert min_split_pos <= optimal_split_pos <= max_split_pos, "out of range"
            assert it.from_ <= optimal_split_pos < it.to
            if not self.is_block_begin(optimal_split_pos):
                # move position before actual instruction (odd op_id)
                optimal_split_pos = (optimal_split_pos - 1) | 1
            else:
                assert optimal_split_pos & 1 == 0, "split pos must be even on block boundary"

            spilled_part = it.split(optimal_split_pos)
            self.append_interval(spilled_part)
            self.assign_spill_slot(spilled_part)
            self.change_spill_state(spilled_part, optimal_split_pos)
            if not self.is_block_begin(optimal_split_pos):
                assert isinstance(it, (SplitParent, SplitChild))
                self.insert_move(optimal_split_pos, it, spilled_part)

            spilled_part.make_current_split_child()
            append_to_handled(spilled_part)

    def assign_spill_slot(self, it: Interval, /):
        """assign the canonical spill slot of the parent (if a part of the interval is already spilled) or allocate a new spill slot"""
        if it.canonical_spill_slot >= 0:
            it.assign_reg(it.canonical_spill_slot)
        else:
            res = self.max_spills + LIR_Opr.n_phyregs + int(len(self.calls) > 0) + max(self.res_on_stack_word_length, len(self.on_stack_arg_vregs))
            self.max_spills += 1
            it.canonical_spill_slot = res
            it.assign_reg(res)

    def change_spill_state(self, it: Interval, spill_pos: int, /):
        match it.spill_state:
            case IntervalSpillState.oneDefinitionFound:
                def_loop_depth = self.block_of_op_with_id[it.split_parent.spill_definition_pos].loop_depth
                spill_loop_depth = self.block_of_op_with_id[spill_pos].loop_depth
                if def_loop_depth < spill_loop_depth:
                    # the loop depth of the spilling position is higher than the loop depth at the definition of the interval 
                    # -> move write to memory out of loop by storing at definition of the interval
                    it.split_parent.spill_state = IntervalSpillState.storeAtDefinition
                else:
                    # the interval is currently spilled only once, so for now there is no
                    # reason to store the interval at the definition
                    it.split_parent.spill_state = IntervalSpillState.oneMoveInserted
            case IntervalSpillState.oneMoveInserted:
                # the interval is spilled more than once, so it is better to store it to memory at the definition
                it.split_parent.spill_state = IntervalSpillState.storeAtDefinition
            case IntervalSpillState.storeAtDefinition | IntervalSpillState.startInMemory | IntervalSpillState.noOptimization | IntervalSpillState.noDefinitionFound:
                ...
    
    def split_and_spill_intersecting_intervals(self, position: int, active: MutableMapping[int, Interval], inactive: MutableMapping[int, Interval], spill_intervals: Sequence[Interval], /, append_to_unhandled: Callable[[SplitChild], None], append_to_handled: Callable[[Interval], None]):
        for it in spill_intervals:
            assert not it.is_fixed
            if it.reg_num in active:
                self.spilt_and_spill_interval(position, it, active, inactive, append_to_unhandled, append_to_handled)
                assert it.to <= position or it.reg_num >= LIR_Opr.n_phyregs
                append_to_handled(it)
                del active[it.reg_num]
            elif it.reg_num in inactive:
                self.spilt_and_spill_interval(position, it, active, inactive, append_to_unhandled, append_to_handled)
                assert it.to <= position or it.reg_num >= LIR_Opr.n_phyregs
                append_to_handled(it)
                del inactive[it.reg_num]
            else:
                assert False, "interval not found"
    
    def insert_move(self, op_id: int, src_it: SplitParent | SplitChild, dst_id: SplitChild, /):
        op_id = (op_id + 1) & ~1
        op_block = self.block_of_op_with_id[op_id]
        assert dst_id.split_parent is src_it.split_parent
        assert 0 < op_id and self.block_of_op_with_id[op_id - 2] == op_block, "cannot insert move at block boundary"
        if op_id - 1 not in self.move_mappings:
            self.move_mappings[op_id - 1] = []
        self.move_mappings[op_id - 1].append((src_it, dst_id))

    def resolve_collect_mappings(self, from_block: BlockBegin, to_block: BlockBegin, nb: int, ns: int, /):
        mappings: list[tuple[SplitParent | SplitChild, SplitChild] | tuple[SplitChild, SplitParent | SplitChild]] = []
        live_at_edge = self.live_in[to_block.block_id]
        assert live_at_edge.issubset(self.live_out[from_block.block_id])
        for x in live_at_edge:
            i = self.intervals[x.reg_num].split_parent
            from_interval = i.split_child_at_op_id(from_block.lir.lir[-1].id + 1, 'output')
            to_interval = i.split_child_at_op_id(to_block.lir.lir[0].id, 'output')
            if from_interval is not to_interval and from_interval.assigned_reg != to_interval.assigned_reg:
                if nb < ns:
                    assert isinstance(from_interval, (SplitParent, SplitChild)) and isinstance(to_interval, SplitChild)
                    mappings.append((from_interval, to_interval))
                else:
                    assert isinstance(from_interval, SplitChild) and isinstance(to_interval, (SplitParent, SplitChild))
                    mappings.append((from_interval, to_interval))

        return mappings
        
    def resolve_dataflow(self):
        linearscan_number = {b.block_id: i for i, b in enumerate(self.blocks)}
        completed = {b.block_id: False for b in self.blocks}
        moves_on_boundary: dict[tuple[int, int], list[tuple[SplitParent | SplitChild, SplitChild] | tuple[SplitChild, SplitParent | SplitChild]]] = {}
        move_buf: dict[int, dict[int, list[tuple[SplitParent | SplitChild, SplitChild] | tuple[SplitChild, SplitParent | SplitChild]]]] = {i: {} for i in range(len(self.blocks))}
        
        for b in self.blocks:
            if len(b.predesessors) == len(b.end.sux) == 1 and len(b.lir.lir) == 2:
                assert isinstance(b.lir.lir[0], LIR_OpLabel)
                assert isinstance(b.lir.lir[-1], LIR_OpGoto)
                pred, sux = b.predesessors[0], b.end.sux[0]
                if not completed[pred.block_id] and not completed[sux.block_id]:
                    completed[b.block_id] = True
                    pred_n, sux_n = linearscan_number[pred.block_id], linearscan_number[sux.block_id]
                    mappings = self.resolve_collect_mappings(pred, sux, pred_n, sux_n)
                    if mappings:
                        n = linearscan_number[b.block_id]
                        first_op = b.lir.lir[0]
                        if first_op.id + 1 not in move_buf[n]:
                            move_buf[n][first_op.id + 1] = []
                        move_buf[n][first_op.id + 1].extend(mappings)
        

        for b in self.blocks:
            if completed[b.block_id]: continue
            nb = linearscan_number[b.block_id]
            for s in b.end.sux:
                ns = linearscan_number[s.block_id]
                pair = (nb, ns)
                if pair not in moves_on_boundary:
                    mappings = self.resolve_collect_mappings(b, s, nb, ns)
                    if mappings:
                        moves_on_boundary[pair] = mappings
        
        self.move_mappings_on_block_boundary.clear()
        self.move_mappings_on_block_boundary.update(moves_on_boundary)
        # self.boundary_move_buf = {k: self.resolve_moves(v) for k, v in self.move_mappings_on_block_boundary.items()}

        for (b, s), moves in self.move_mappings_on_block_boundary.items():
            if len(self.blocks[b].end.sux) == 1:
                last_op = self.blocks[b].lir.lir[-1]
                assert isinstance(last_op, LIR_OpGoto)
                if last_op.id - 1 not in move_buf[b]:
                    move_buf[b][last_op.id - 1] = []
                move_buf[b][last_op.id - 1].extend(moves)

            elif len(self.blocks[s].predesessors) == 1:
                first_op = self.blocks[s].lir.lir[0]
                assert isinstance(first_op, LIR_OpLabel)
                if first_op.id + 1 not in move_buf[s]:
                    move_buf[s][first_op.id + 1] = []
                move_buf[s][first_op.id + 1].extend(moves)
            else:
                raise ValueError("critical edge not resolved")
            
        for op_id, moves in self.move_mappings.items():
            i = linearscan_number[self.block_of_op_with_id[op_id].block_id]
            if op_id not in move_buf[i]:
                move_buf[i][op_id] = []
            move_buf[i][op_id].extend(moves)

        move_buf2 = {k: {op_id: self.resolve_moves(op_id, v) for op_id, v in moves.items()} for k, moves in move_buf.items()}
        for i in move_buf2:
            wait_to_insert = sorted(move_buf2[i].items(), key=lambda x: x[0], reverse=True)
            if len(wait_to_insert) > 0:
                logger.debug(f"{self.f.name}: block {self.blocks[i]} has {len(wait_to_insert)} moves to insert")
                for op_id, moves in wait_to_insert:
                    first_op_id = self.blocks[i].lir.lir[0].id
                    idx = (op_id + 1 - first_op_id) // 2
                    self.blocks[i].lir.lir[idx:idx] = moves

    def resolve_moves(self, op_id: int, moves: Sequence[tuple[SplitParent | SplitChild, SplitChild] | tuple[SplitChild, SplitParent | SplitChild]], /):
        # for op_id, moves in sorted(self.move_mappings.items(), key=lambda x: x[0], reverse=True):
        froms = [fst for fst, _ in moves]
        tos = [snd for _, snd in moves]
        i = 0
        dels = (i for i in reversed(range(len(froms))) if froms[i].assigned_reg == tos[i].assigned_reg)
        for i in dels:
            del froms[i], tos[i]
        srcs = [f.assigned_reg for f in froms]
        dsts = [t.assigned_reg for t in tos]
        blocked = [True] * len(srcs)
        processed = [False] * len(srcs)
        move_buf: list[LIR_OpMove | LIR_OpSpill | LIR_OpRestore] = []
        while (i:=next((i for i in range(len(dsts)) if not processed[i] and (dsts[i] not in srcs or not blocked[srcs.index(dsts[i])])), None)) is not None: 
            from_i, to_i = froms[i], tos[i]
            if 0 <= from_i.assigned_reg < LIR_Opr.n_phyregs:
                src = LIR_PhyReg.factory(from_i.assigned_reg)
            else:
                src = LIR_StackSlot(from_i.assigned_reg - LIR_Opr.n_phyregs, from_i.type)
            if 0 <= tos[i].assigned_reg < LIR_Opr.n_phyregs:
                dst = LIR_PhyReg.factory(to_i.assigned_reg)
            else:
                dst = LIR_StackSlot(to_i.assigned_reg - LIR_Opr.n_phyregs, to_i.type)
            if isinstance(src, LIR_StackSlot):
                assert isinstance(dst, (LIR_CpuReg, LIR_FloatReg))
                move_buf.append(LIR_OpRestore(src, dst))
            elif isinstance(dst, LIR_StackSlot):
                assert isinstance(src, (LIR_CpuReg, LIR_FloatReg))
                move_buf.append(LIR_OpSpill(src, dst))
            else:
                move_buf.append(LIR_OpMove(src, dst))
            move_buf[-1].id = op_id
            blocked[i] = False
            processed[i] = True
        
        if not all(processed):
            raise NotImplementedError()
        return move_buf

    def color_lir_opr(self, reg_num: int, op_id: int, mode: Literal['input', 'output'], /):
        if 0 <= reg_num < LIR_Opr.n_cpu_regs:
            return LIR_CpuReg(reg_num)
        elif LIR_Opr.n_cpu_regs <= reg_num < LIR_Opr.n_phyregs:
            return LIR_FloatReg(reg_num)
        
        it = self.intervals[reg_num]
        a = it.split_parent.split_child_at_op_id(op_id, mode)
        assert a.assigned_reg >= 0
        if 0 <= a.assigned_reg < LIR_Opr.n_cpu_regs:
            return LIR_CpuReg(a.assigned_reg)
        elif LIR_Opr.n_cpu_regs <= a.assigned_reg < LIR_Opr.n_phyregs:
            return LIR_FloatReg(a.assigned_reg)
        else:
            word_offset = a.assigned_reg - LIR_Opr.n_phyregs
            return LIR_StackSlot(word_offset, a.type)
    
    def verify(self):
        for ia in self.intervals.values():
            assert ia.assigned_reg != -1
            for ib in self.intervals.values():
                assert ib.assigned_reg != -1
                if ia is not ib and ia.assigned_reg == ib.assigned_reg:
                    assert ia.intersects(ib) is None

        for i in self.move_mappings.values():
            for src, dst in i:
                assert (0 <= src.assigned_reg < LIR_Opr.n_phyregs) or (0 <= dst.assigned_reg < LIR_Opr.n_phyregs) or (src.assigned_reg == dst.assigned_reg)
        
    def eliminate_spill_moves(self):
        pass

    def calculate_frame_size(self):
        framesize = max(len(self.on_stack_arg_vregs), self.res_on_stack_word_length) + int(len(self.calls) > 0) + self.max_spills
        s: set[int] = set()
        for it in self.intervals:
            o = self.intervals[it]
            if 0 <= o.assigned_reg < LIR_Opr.n_cpu_regs and LIR_CpuReg.abi_name[o.assigned_reg] in LIR_CpuReg.callee_saved_names:
                s.add(o.assigned_reg)
            elif LIR_Opr.n_cpu_regs <= o.assigned_reg < LIR_Opr.n_phyregs:
                i = o.assigned_reg - LIR_Opr.n_cpu_regs
                if LIR_FloatReg.abi_name[i] in LIR_FloatReg.callee_saved_names:
                    s.add(o.assigned_reg)

        framesize += len(s)

        padding = 0
        while framesize % 4 != 0:
            framesize += 1
            padding += 1
        
        self.framesize = framesize
        self.padding = padding
        self.saved_cpu_regs = [i for i in range(LIR_Opr.n_cpu_regs) if i in s]
        self.saved_float_regs = [i for i in range(LIR_Opr.n_cpu_regs, LIR_Opr.n_phyregs) if i in s]

    def assign_reg_num(self):
        for b in self.blocks:
            for i in reversed(range(len(b.lir.lir))):
                    # input_oprs = b.lir.lir[i].input_oprs()
                    # tmp_oprs = b.lir.lir[i].tmp_oprs()
                    l = b.lir.lir[i]
                    output_oprs = l.output_oprs()
                    m = vars(l)
                    for k in m:
                        v = m[k]
                        if isinstance(v, LIR_VirtualReg):
                            m[k] = self.color_lir_opr(v.reg_num, l.id, 'output' if v in output_oprs else 'input')
                    
                    if isinstance(l, (LIR_OpMove, LIR_OpSpill, LIR_OpRestore)):
                        if l.opr is l.result or isinstance(l.opr, LIR_StackSlot) and isinstance(l.result, LIR_StackSlot) and l.opr.stack_word_offset == l.result.stack_word_offset:
                            del b.lir.lir[i]

            for i in reversed(range(len(b.lir.lir))):
                l = b.lir.lir[i]
                if isinstance(l, LIR_OpMove):
                    if isinstance(l.result, LIR_StackSlot):
                        assert isinstance(l.opr, LIR_PhyReg)
                        id = l.id
                        b.lir.lir[i] = LIR_OpSpill(l.opr, l.result)
                        b.lir.lir[i].id = id
                    elif isinstance(l.opr, LIR_StackSlot):
                        assert isinstance(l.result, LIR_PhyReg)
                        id = l.id
                        b.lir.lir[i] = LIR_OpRestore(l.opr, l.result)
                        b.lir.lir[i].id = id
                        
        return

    def do_linear_scan(self):
        self.detect_loops()
        self.compute_block_order()
        self.number_operations()
        self.build_intervals()
        self.sort_intervals_before_allocation()
        self.allocate_registers()
        self.resolve_dataflow()
        self.sort_intervals_after_allocation()
        self.verify()
        self.eliminate_spill_moves()
        self.assign_reg_num()
        self.calculate_frame_size()
                 

class MoveResolver:
    def __init__(self, ls: LinearScan, /):
        self.ls = ls
        


class LIRPrinter:
    def __init__(self, file: TextIOWrapper):
        self.file = file

    def print_function(self, ls: LinearScan, /):
        file = self.file
        file.write('LIR:\n')
        if ls.f.formal_arg_vregs:
            file.write(f'LIR formal arguments:\n')
            for i, a in enumerate(ls.f.formal_arg_vregs):
                file.write(f' {i:>4}   {a}\n')
        else:
            file.write('No formal arguments\n')
        file.write(f'\nblock order of {ls.f.name}: total {len(ls.blocks)} blocks\n')
        file.write('\n            ')
        file.write(f', '.join(f'{str(b):4}' for b in ls.blocks))
        file.write('\nloop_depth: ')
        file.write(f'  '.join(f'{b.loop_depth or "":4}' for b in ls.blocks))
        file.write('\n            ')
        file.write(f'  '.join(f'{"HEAD" if b.is_loop_header else " END" if b.is_loop_end else "    "}' for b in ls.blocks))
        file.write('\nDominators:\n')
        file.write('__blockid__dominators__\n')
        for k, v in ls.dominators.items():
                file.write(f'  {"B" + str(k):<9} {v}\n')
        file.write('\n')
        for b in ls.blocks:
            live_in = sorted(ls.live_in[b.block_id], key=lambda x: x.reg_num)
            live_out = sorted(ls.live_out[b.block_id], key=lambda x: x.reg_num)
            self.file.write(f'B{b.block_id}:')
            if b.predesessors:
                self.file.write(f'  pred: {", ".join(map(str, b.predesessors))}')
            if b.end.sux:
                self.file.write(f'  sux: {", ".join(map(str, b.end.sux))}')
            if b.is_loop_header:
                self.file.write(f'  loop_header, loop_depth: {b.loop_depth}, loop_index: {b.loop_index}')
            if b.is_loop_end:
                self.file.write(f'  loop_end, loop_depth: {b.loop_depth}, loop_index: {b.loop_index}')
            self.file.write('\n')
            self.file.write(f'live_in: {", ".join(map(str, live_in))}\n')
            self.file.write(f'live_out: {", ".join(map(str, live_out))}\n')
            self.file.write(f'___id___Operations___________________________\n')
            for l in b.lir.lir:
                self.file.write(f' {l.id:>4}   {l!r}\n')
            self.file.write('\n')
            pm = b.lir.patch_moves
            if pm:
                self.file.write('  Patch moves:\n')
            else:
                self.file.write('  No patch moves\n')
            for m in pm:
                self.file.write(f'    {m}\n')
        file.write('\n')
        file.write('Intervals:\n')
        file.write(f'Max Spills: {ls.max_spills}\n')
        file.write(f'reg_num {"abi_name"} {"spill_state":>15} {"type":>5} {"assigend_reg":>7} {"split_parent"} ranges\n')
        for i, interval in sorted(ls.intervals.items(), key=lambda x: (x[1].from_, x[0])):
            file.write(f'{i:>7} ')
            if interval.is_fixed:
                if i < 32:
                    file.write(f'{LIR_CpuReg.abi_name[i]:>8} ')
                else:
                    file.write(f'{LIR_FloatReg.abi_name[i - 32]:>8} ')
            else:
                file.write(f'{"":8} ')
            match interval.spill_state:
                case IntervalSpillState.noDefinitionFound:
                    file.write(f'{"":>15}')
                case IntervalSpillState.oneDefinitionFound:
                    file.write(f'{"1 def":>15}')
                case IntervalSpillState.oneMoveInserted:
                    file.write(f'{"1 move inserted":>15}')
                case IntervalSpillState.storeAtDefinition:
                    file.write(f'{"store at def":>15}')
                case IntervalSpillState.startInMemory:
                    file.write(f'{"start in mem":>15}')
                case IntervalSpillState.noOptimization:
                    file.write(f'{"no opt":>15}')
            if interval.is_fixed:
                file.write(' ' * 9)
            else:
                s = {BasicType.T_INT: ' int ', BasicType.T_FLOAT: 'float'}
                file.write(f' {s[interval.type]:>7} ')
            if 0 <= interval.assigned_reg < LIR_Opr.n_cpu_regs:
                file.write(f'  {LIR_CpuReg.abi_name[interval.assigned_reg]:>7}')
            elif LIR_Opr.n_cpu_regs <= interval.assigned_reg < LIR_Opr.n_phyregs:
                file.write(f'  {LIR_FloatReg.abi_name[interval.assigned_reg - LIR_Opr.n_cpu_regs]:>7}')
            elif LIR_Opr.n_phyregs <= interval.assigned_reg:
                file.write(f'  stack:{interval.assigned_reg - LIR_Opr.n_phyregs}')
            else:
                file.write(f'  {"":7}')
            if interval.split_parent is not interval:
                file.write(f'  {interval.split_parent.reg_num:>5}       ')
            else:
                file.write(f'  {"":5}       ')
            file.write(f'    ')
            file.write(f'  {interval.ranges}')
            file.write(f'  {interval.use_positions}\n')
        
        if ls.move_mappings:
            file.write('Move mappings:\n')
            file.write('__opid_____from________to______\n')
            for k, v in sorted(ls.move_mappings.items()):
                for src, dst in v:
                    file.write(f'  {k:>5}   {src.reg_num} -> {dst.reg_num}\n')

class LIROptimizer:
    def __init__(self, ls: LinearScan, /):
        self.ls = ls

    def remove_indirect_jumps(self):
        """the mapping between HIR block and LIR block may be broken"""
        # use_count = {b.block_id: 0 for b in self.ls.blocks}
        # for b in self.ls.blocks:
        #     match b.lir.lir:
        #         case [*_, LIR_OpBranCond() as bc, LIR_OpGoto() as goto]:
        #             use_count[bc.target.block_id] += 1
        #             use_count[goto.target.block_id] += 1
        #         case [*_, LIR_OpGoto() as goto]:
        #             use_count[goto.target.block_id] += 1
        #         case _: ...
        # dels: set[int] = set()
        # updated = True
        # while updated:
        #     updated = False
        #     dels.clear()
        #     for b in self.ls.blocks:
        #         ops = b.lir.lir
        #         assert isinstance(ops[0], LIR_OpLabel) and isinstance(ops[-1], (LIR_OpGoto, LIR_OpReturn))
        #         if isinstance(goto:=ops[-1], LIR_OpGoto):
        #             target_lir = goto.target.lir.lir
        #             match target_lir:
        #                 case [LIR_OpLabel(), LIR_OpGoto() as goto2]:
        #                     ops[-1] = LIR_OpGoto(goto2.target)
        #                     ops[-1].id = goto.id
        #                     use_count[goto.target.block_id] -= 1
        #                     if use_count[goto.target.block_id] == 0:
        #                         dels.add(goto.target.block_id)
        #                 case
        #     if dels:
        #         updated = True
        #         for i in sorted(dels, reverse=True):
        #             del self.ls.blocks[i]

class Assembler:
    float_table: dict[float, str] = {}

    def __init__(self, ls: LinearScan, /):
        self.ls = ls

    def emit_function(self, /):
        buf: list[str] = []
        if not self.ls.f.name.is_main():
            buf.append(f'.globl {self.ls.f.name}')
            buf.append(f'.type {self.ls.f.name}, @function')
            buf.append(f'{self.ls.f.name}:')
        else:
            buf.extend(('.globl main', '.type main, @function', 'main:'))
        arglen = max(len(self.ls.on_stack_arg_vregs), self.ls.res_on_stack_word_length)
        if self.ls.framesize:
            buf.append(f'# framesize: {self.ls.framesize}, padding: {self.ls.padding}')
            buf.append(f'    addi sp, sp, {-self.ls.framesize * 4}')
            if self.ls.calls:
                has_call = True
                buf.append(f'    sw ra, {(self.ls.framesize - arglen - 1) * 4}(sp)')
            else:
                has_call = False
            k = [4 * (self.ls.framesize - arglen - has_call - 1 - i) for i in range(len(self.ls.saved_cpu_regs) + len(self.ls.saved_float_regs))]
            for i, j in zip(self.ls.saved_cpu_regs, k):
                buf.append(f'    sw {LIR_CpuReg.abi_name[i]}, {j}(sp)')
            for i, j in zip(self.ls.saved_float_regs, k[len(self.ls.saved_cpu_regs):]):
                buf.append(f'    fsw {LIR_FloatReg.abi_name[i - LIR_Opr.n_cpu_regs]}, {j}(sp)')
        else:
            k = ()
            assert not self.ls.saved_cpu_regs and not self.ls.saved_float_regs
        def epilog():
            if self.ls.framesize:
                for i, j in zip(self.ls.saved_cpu_regs, k):
                    buf.append(f'    lw {LIR_CpuReg.abi_name[i]}, {j}(sp)')
                for i, j in zip(self.ls.saved_float_regs, k[len(self.ls.saved_cpu_regs):]):
                    buf.append(f'    flw {LIR_FloatReg.abi_name[i - LIR_Opr.n_cpu_regs]}, {j}(sp)')
                if self.ls.calls:
                    buf.append(f'    lw ra, {(self.ls.framesize - arglen - 1) * 4}(sp)')
                buf.append(f'    addi sp, sp, {self.ls.framesize * 4}')

        for i, b in enumerate(self.ls.blocks):
            buf.append(f'B{b.block_id}:')
            if b.is_loop_header:
                buf[-1] += f'  # loop header, loop_depth: {b.loop_depth}, loop_index: {b.loop_index}'
            elif b.is_loop_end:
                buf[-1] += f'  # loop end, loop_depth: {b.loop_depth}, loop_index: {b.loop_index}'
            elif b.loop_depth != 0:
                buf[-1] += f'  # loop body, loop_depth: {b.loop_depth}, loop_index: {b.loop_index}'
            if b.predesessors:
                buf[-1] += f'  #  pred: {", ".join(map(str, b.predesessors))}'
            for s in self.emit(b.lir.lir, self.ls.blocks[i+1] if i + 1 < len(self.ls.blocks) else None, epilog, len(k), arglen, len(self.ls.calls) > 0):
                buf.append(s)
        return buf
    def stack_slot_offset(self, slot: LIR_StackSlot, n_saved_regs: int, arglen: int, has_calls: bool, /):
        if slot.stack_word_offset < 0:
            return slot.stack_word_offset * 4
        elif slot.stack_word_offset < arglen:
            res = (self.ls.framesize - 1 - slot.stack_word_offset) * 4
            assert res >= 0
            return res
        else:
            res = (self.ls.framesize - n_saved_regs - 1 - slot.stack_word_offset) * 4
            assert res >= 0
            return res
    
    def emit(self, ops: Iterable[LIR_Op], next_block: BlockBegin | None, epilog: Callable[[], None], n_saved_regs: int, arglen: int, has_calls: bool, /):
        for op in ops:
            match op:
                case LIR_OpLabel():
                    ...
                case LIR_OpMove(opr=LIR_CpuReg() as opr, result=LIR_CpuReg() as result):
                    yield f'    mv {result}, {opr}'
                case LIR_OpMove(opr=LIR_FloatReg() as opr, result=LIR_FloatReg() as result):
                    yield f'    fmv.s {result}, {opr}'
                case LIR_OpMove(opr=LIR_Const() as opr, result=LIR_PhyReg() as result):
                    assert isinstance(opr.value, int)
                    yield f'    li {result}, {int(opr.value)}'
                case LIR_OpRestore(opr=LIR_StackSlot() as opr, result=LIR_CpuReg() as result):
                    offset = self.stack_slot_offset(opr, n_saved_regs, arglen, has_calls)
                    yield f'    lw {result}, {offset}(sp) # {opr!r}'
                case LIR_OpRestore(opr=LIR_StackSlot() as opr, result=LIR_FloatReg() as result):
                    offset = self.stack_slot_offset(opr, n_saved_regs, arglen, has_calls)
                    yield f'    flw {result}, {offset}(sp) # {opr!r}'
                case LIR_OpSpill(opr=LIR_CpuReg() as opr, stack_slot=LIR_StackSlot() as result):
                    offset = self.stack_slot_offset(result, n_saved_regs, arglen, has_calls)
                    yield f'    sw {opr}, {offset}(sp) # {result!r}'
                case LIR_OpSpill(opr=LIR_FloatReg() as opr, stack_slot=LIR_StackSlot() as result):
                    offset = self.stack_slot_offset(result, n_saved_regs, arglen, has_calls)
                    yield f'    fsw {opr}, {offset}(sp) # {result!r}'
                case LIR_OpUnary() if op.is_call:
                    yield f'    call {op.op}'
                case LIR_OpUnary():
                    yield f'    {op.op} {op.result}, {op.opr}'
                case LIR_OpReturn():
                    epilog()
                    yield '    ret'
                case LIR_OpAllocArray():
                    suffix = ''.join('0' if init.basic_type is BasicType.T_INT else '1' for init in op.inits)
                    yield f'    call create_array_{suffix}_{op.on_stack_res_length}'

                case LIR_OpStoreWordGlobal():
                    yield f'    lui {op.tmp}, %hi({op.global_var.label})'
                    if op.global_var.word_offset:
                        yield f'    addi {op.tmp}, {op.tmp}, {4 * op.global_var.word_offset}'
                    yield f'    sw {op.opr}, %lo({op.global_var.label})({op.tmp})'

                case LIR_OpLoadWordGlobal():
                    yield f'    lui {op.tmp}, %hi({op.global_var.label})'
                    if op.global_var.word_offset:
                        yield f'    addi {op.tmp}, {op.tmp}, {4 * op.global_var.word_offset}'
                    yield f'    lw {op.result}, %lo({op.global_var.label})({op.tmp})'

                case LIR_OpLoadFloatImm():
                    if op.imm == 0.0:
                        yield f'    fmv.w.x {op.result}, zero'
                    elif op.imm == 1.0:
                        yield f'    lui {op.tmp}, 0x3f800'
                        yield f'    fmv.w.x {op.result}, {op.tmp}'
                    elif op.imm == -1.0:
                        yield f'    lui {op.tmp}, 0xbf800'
                        yield f'    fmv.w.x {op.result}, {op.tmp}'
                    else:
                        if op.imm not in self.float_table:
                            h: int = unpack('<I', pack('<f', op.imm))[0]
                            self.float_table[op.imm] = f'LC_{hex(h)}'
                        yield f'    lui {op.tmp}, %hi({self.float_table[op.imm]})'
                        yield f'    flw {op.result}, %lo({self.float_table[op.imm]})({op.tmp}) # {repr(op.imm)}'
                case LIR_OpLoadWord(result=LIR_CpuReg() as result):
                    yield f'    lw {result}, {4 * op.offset}({op.opr})'

                case LIR_OpLoadWord(result=LIR_FloatReg() as result):
                    yield f'    flw {result}, {4 * op.offset}({op.opr})'

                case LIR_OpStoreWord(opr1=LIR_CpuReg() as opr1, opr2=LIR_CpuReg() as opr2):
                    yield f'    sw {opr1}, {4 * op.offset}({opr2})'

                case LIR_OpStoreWord(opr1=LIR_FloatReg() as opr1, opr2=LIR_CpuReg() as opr2):
                    yield f'    fsw {opr1}, {4 * op.offset}({opr2})'
                
                case LIR_OpArith() | LIR_OpFloatArith() | LIR_OpFloatCmp():
                    yield f'    {op.op} {op.result}, {op.opr1}, {op.opr2}'

                case LIR_OpArithImm():
                    yield f'    {op.op} {op.result}, {op.opr}, {op.imm}'
                
                case LIR_OpConvert(opr=LIR_CpuReg() as opr, result=LIR_FloatReg() as result):
                    yield f'    fcvt.s.w {result}, {opr}'
                
                case LIR_OpConvert(opr=LIR_FloatReg() as opr, result=LIR_CpuReg() as result):
                    yield f'    fcvt.w.s {result}, {opr}'
                case LIR_OpCall():
                    yield f'    call {op.callee.name}'
                
                case LIR_OpBranCond():
                    yield f'    {op.op} {op.opr1}, {op.opr2}, {op.target!r}'
                
                case LIR_OpGoto():
                    if next_block is None or next_block.block_id != op.target.block_id:
                        yield f'    j {op.target!r}'
                    
                case LIR_OpReadFloat():
                    if qemu:
                        assert op.result is LIR_FloatReg('fa0')
                        yield f'    call read_float'
                    else:
                        yield f'    cin.float {op.result}'
                case LIR_OpReadInt():
                    if qemu:
                        assert op.result is LIR_CpuReg('a0')
                        yield f'    call read_int'
                    else:
                        yield f'    cin.int {op.result}'
                case LIR_OpPrintByte():
                    if qemu:
                        assert op.opr is LIR_CpuReg('a0')
                        yield f'    call putchar'
                    else:
                        yield f'    out {op.opr}'
                case LIR_OpPrintInt():
                    assert isinstance(op.opr, LIR_CpuReg) and op.opr.reg_num == 10
                    yield f'    call print_int'
                case LIR_OpComment():
                    yield f'    # {op.comment}'
                case _:
                    raise NotImplementedError(op)

