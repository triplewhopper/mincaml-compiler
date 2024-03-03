from dataclasses import dataclass
from abc import ABC, abstractmethod
from enum import Enum, auto
from transform.closure.basictype import BasicType
from transform.closure.lir_opr import LIR_Opr, LIR_CpuReg, LIR_FloatReg, LIR_VirtualReg
from typing import Literal, final, overload, ClassVar, Self
from bisect import bisect_left, bisect_right

class IntervalSpillState(Enum):
    noDefinitionFound = auto()
    oneDefinitionFound = auto()
    oneMoveInserted = auto()
    storeAtDefinition = auto()
    startInMemory = auto()
    noOptimization = auto()

    def __le__(self, other: 'IntervalSpillState'):
        return self.value <= other.value


class IntervalUseKind(Enum):
    loopEndMarker = auto()
    shouldHaveRegister = auto()
    mustHaveRegister = auto()

    def __repr__(self):
        return {
            IntervalUseKind.loopEndMarker: "loopEndMarker",
            IntervalUseKind.shouldHaveRegister: "should",
            IntervalUseKind.mustHaveRegister: "must"
        }[self]

    def __lt__(self, other: 'IntervalUseKind'):
        return self.value < other.value

    def __le__(self, other: 'IntervalUseKind'):
        return self.value <= other.value

class IntervalState(Enum):
    unhandled = auto()
    active = auto()
    inactive = auto()
    handled = auto()

    def __le__(self, other: 'IntervalState'):
        return self.value <= other.value


@dataclass(order=True, slots=True, unsafe_hash=True)
class Range:
    MAX: ClassVar[Literal[1073741284]] = 2**30
    from_: int
    to: int

    def __repr__(self):
        return f"[{self.from_}, {self.to}["
        # if self is not sentinel:
        #     return f"[{self.from_}, {self.to}["
        # return "sentinel"
    
    def isdisjoint(self, other: 'Range'):
        return self.to <= other.from_ or other.to <= self.from_


# sentinel: Final = Range(Range.MAX, Range.MAX)

class Interval(ABC):
    def __init__(self, reg_num: int, /, type: BasicType):
        self.__reg_num = reg_num
        self.__type = type
        # self.ranges: list[Range] = [sentinel]
        self.ranges: list[Range] = []
        self.use_positions: list[tuple[int, IntervalUseKind]] = []
        self._register_hint: 'SplitParent | None' = None
        self._assigned_reg = -1
        self._state: IntervalState | None = None
        # self._current_range = self.ranges[0]


    @property
    def reg_num(self): return self.__reg_num
    @property
    def type(self):
        assert self.__reg_num >= LIR_Opr.vreg_base
        return self.__type
    @property
    def state(self):
        return self._state
    @state.setter
    def state(self, state: IntervalState):
        self._state = state

    def set_register_hint(self, hint: 'SplitParent'):
        self._register_hint = hint
    @overload
    def register_hint(self, search_split_child: Literal[False]) -> 'SplitParent | None': ...

    @overload
    def register_hint(self, search_split_child: bool) -> 'Interval | None': ...

    def register_hint(self, search_split_child: bool) -> 'Interval | None':
        if not search_split_child:
            return self._register_hint
        if self._register_hint is not None:
            if 0 <= self._register_hint.assigned_reg < LIR_Opr.n_phyregs:
                return self._register_hint
            elif len(self._register_hint.split_children) > 0:
                # search the first split child that has a register assigned
                for child in self._register_hint.split_children:
                    if 0 <= child.assigned_reg < LIR_Opr.n_phyregs:
                        return child
        return None

    def assign_reg(self, reg: int, /):
        assert not self.is_fixed or reg == self.reg_num, "cannot assign register to fixed interval"
        assert self._assigned_reg == -1 or reg == self.canonical_spill_slot, "register already assigned"
        self._assigned_reg = reg
    
    @property
    @abstractmethod
    def split_parent(self) -> 'SplitParent':
        ...

    def verify(self):
        assert self.reg_num >= 0
        assert len(self.ranges) > 0
        assert len(self.use_positions) > 0
        assert len(self.use_positions) == len(set(self.use_positions))
        assert len(self.ranges) == len(set(self.ranges))
        self.use_positions.sort()
        self.ranges.sort()
        for r in self.ranges:
            assert r.from_ <= r.to
        for i in range(len(self.ranges) - 2):
            assert self.ranges[i].to <= self.ranges[i + 1].from_
        for i in range(1, len(self.ranges) - 1):
            assert self.ranges[i - 1].to < self.ranges[i].from_
        
    def covers(self, op_id: int, mode: Literal['input', 'output']):
        if self.ranges:
            if op_id > self.to: return False
            i = bisect_left(self.ranges, op_id, key=lambda r: r.to)
            cur = self.ranges[i]
            assert cur.to >= op_id, "bisect_left returned wrong index"
            assert i == len(self.ranges) - 1 or cur.to < self.ranges[i+1].from_, 'ranges not separated'
            if mode == 'output':
                return cur.from_ <= op_id < cur.to
            else:
                return cur.from_ <= op_id <= cur.to
        return False
    
    def intersects(self, it: 'Interval'):
        i, j = 0, 0
        while i < len(self.ranges) and j < len(it.ranges):
            if self.ranges[i].to <= it.ranges[j].from_:
                i += 1
            elif it.ranges[j].to <= self.ranges[i].from_:
                j += 1
            else:
                return max(self.ranges[i].from_, it.ranges[j].from_)
        return None
    
    def intersects_any_children_of(self, parent: 'SplitParent'):
        if self.intersects(parent):
            return True
        for child in parent.split_children:
            if self.intersects(child):
                return True
        return False

    def has_hole_between(self, from_: int, to: int):
        assert self.from_ <= from_ < to <= self.to
        for cur in self.ranges:
            if from_ < cur.from_: return True
            if to <= cur.to: return False
            if from_ <= cur.to: return True
        return False
    
    def first_usage(self, min_use_kind: IntervalUseKind):
        assert self.is_virtual, 'cannot access use positions of fixed intervals'
        for pos, kind in reversed(self.use_positions):
            if min_use_kind <= kind:
                return pos
        return Range.MAX
            
    def next_usage(self, min_use_kind: IntervalUseKind, from_: int):
        assert self.is_virtual, 'cannot access use positions of fixed intervals'
        for pos, kind in reversed(self.use_positions):
            if from_ <= pos and min_use_kind <= kind:
                return pos
        return Range.MAX
    
    def next_usage_exact(self, exact_use_kind: IntervalUseKind, from_: int):
        assert self.is_virtual, 'cannot access use positions of fixed intervals'
        for pos, kind in reversed(self.use_positions):
            if from_ <= pos and kind == exact_use_kind:
                return pos
        return Range.MAX
    
    def previous_usage(self, min_use_kind: IntervalUseKind, from_: int):
        assert self.is_virtual, 'cannot access use positions of fixed intervals'
        prev = 0
        for pos, kind in reversed(self.use_positions):
            if from_ < pos:
                return prev
            if min_use_kind <= kind:
                prev = pos
        return prev
    
    def add_range(self, from_: int, to: int):
        assert 0 <= from_ < to, f"invalid range: [{from_}, {to}["
        assert len(self.ranges) <= 1 or len(self.ranges) > 1 and to < self.ranges[1].from_, "not inserting at begin of interval"
        if len(self.ranges) > 0 and self.first_range.from_ <= to:
            # join intersecting ranges
            self.first_range.from_ = min(self.first_range.from_, from_)
            self.first_range.to = max(self.first_range.to, to)
        else:
            self.ranges.insert(0, Range(from_, to))
        
    def add_use_pos(self, pos: int, use_kind: IntervalUseKind | None):
        """Add a use position to the interval. Do nothing when use_kind is `None` or `self` is a fixed interval."""
        assert self.covers(pos, 'input'), f"use pos {pos} not covered by {self}"
        if use_kind is not None and self.reg_num >= 100:
            if len(self.use_positions) == 0 or self.use_positions[-1][0] > pos:
                self.use_positions.append((pos, use_kind))
            elif self.use_positions[-1][1] < use_kind:
                assert self.use_positions[-1][0] == pos, "list not sorted"
                self.use_positions[-1] = (pos, use_kind)

    @property
    @abstractmethod
    def canonical_spill_slot(self) -> int:
        ...

    @canonical_spill_slot.setter
    @abstractmethod
    def canonical_spill_slot(self, value: int):
        ...
    
    @property
    def is_fixed(self):
        return 0 <= self.reg_num < LIR_Opr.n_phyregs
    
    @property
    def is_virtual(self):
        return LIR_Opr.vreg_base <= self.reg_num
    
    @property
    def first_range(self):
        return self.ranges[0]

    @property
    def from_(self):
        return self.ranges[0].from_
    
    @property
    def to(self):
        last = self.ranges[-1]
        return last.to
    
    def rewind_range(self):
        self._current_range = self.ranges[0]

    @property
    def assigned_reg(self):
        return self._assigned_reg

    @property
    @abstractmethod
    def spill_state(self) -> IntervalSpillState:
        ...

    @property
    def always_in_memory(self):
        return self.spill_state in (IntervalSpillState.storeAtDefinition, IntervalSpillState.startInMemory)
    
    @property
    def insert_move_when_activated(self) -> bool:
        return False

    def split(self, split_pos: int):
        assert self.is_virtual, "cannot split fixed interval"
        assert self.ranges, "cannot split empty interval"
        child = SplitChild(LIR_VirtualReg(self.__type), self.split_parent)
        i = bisect_right(self.ranges, split_pos, key=lambda r: r.to)
        assert i < len(self.ranges), "split interval after end of last range"
        if self.ranges[i].from_ < split_pos:
            child.ranges.append(Range(split_pos, self.ranges[i].to))
            child.ranges.extend(self.ranges[i+1:])
            self.ranges[i].to = split_pos
            self.ranges[i+1:] = ()
        else:
            assert 0 < i, "split before start of first range"
            child.ranges.extend(self.ranges[i:])
            self.ranges[i:] = ()
        start_idx = bisect_right(self.use_positions, -split_pos, key=lambda x: -x[0])
        child.use_positions.extend(self.use_positions[:start_idx])
        self.use_positions[:start_idx] = ()
        assert not child.use_positions or child.use_positions[-1][0] >= split_pos
        assert not self.use_positions or split_pos > self.use_positions[0][0]
        return child



@final
class SplitParent(Interval):
    def __init__(self, reg_num: int, /, type: BasicType):
        super().__init__(reg_num, type)
        self.split_children: list[SplitChild] = []
        self._current_split_child: SplitChild | Self = self
        self._canonical_spill_slot = -1
        self._spill_state: IntervalSpillState = IntervalSpillState.noDefinitionFound
        self._spill_definition_pos = -1
    
    @property
    def split_parent(self):
        return self
    
    @property
    def current_split_child(self):
        return self._current_split_child
    
    def make_current_split_child(self, child: 'SplitChild'):
        assert child.split_parent is self and child in self.split_children, "child not in split_children"
        self._current_split_child = child
    
    @property
    def canonical_spill_slot(self):
        return self._canonical_spill_slot
    
    @canonical_spill_slot.setter
    def canonical_spill_slot(self, value: int):
        assert self._canonical_spill_slot == -1, "canonical_spill_slot already set"
        self._canonical_spill_slot = value

    @property
    def spill_state(self):
        return self._spill_state
    
    @spill_state.setter
    def spill_state(self, state: IntervalSpillState):
        assert self._spill_state <= state, "state cannot decrease"
        self._spill_state = state

    @property
    def spill_definition_pos(self):
        return self._spill_definition_pos
    
    @spill_definition_pos.setter
    def spill_definition_pos(self, pos: int):
        assert self._spill_definition_pos == -1, "cannot set spill_definition_pos twice"
        self._spill_definition_pos = pos
    
    def split_child_at_op_id(self, op_id: int, mode: Literal['input', 'output']):
        assert op_id >= 0, 'this method cannot be called for spill moves'
        if not self.split_children:
            assert self.covers(op_id, mode), f"interval {self} does not cover op_id {op_id}"
            return self
        else:
            if self.covers(op_id, mode):
                return self
            result = None
            to_offset = 0 if mode == 'output' else 1
            for i, cur in enumerate(self.split_children):
                if cur.from_ <= op_id < cur.to + to_offset:
                    if i > 0:
                        self.split_children[0], self.split_children[i] = self.split_children[i], self.split_children[0]
                    result = cur
                    break
            assert result is not None, f"no matching interval found for op_id {op_id}"
            assert result.covers(op_id, mode), f"interval {result} does not cover op_id {op_id}"
            return result
        
    def split_child_before_op_id(self, op_id: int):
        assert 0 <= op_id, "invalid op_id"
        parent = self.split_parent
        res = None
        if self.to <= op_id: res = self
        for child in reversed(parent.split_children):
            if child.to <= op_id and (res is None or res.to < child.to):
                res = child
        assert res is not None, "no split child found"
        return res
    
    def __repr__(self):
        if self.is_fixed:
            if self.reg_num < LIR_Opr.n_cpu_regs:
                return f"Fixed({self.reg_num}({LIR_CpuReg(self.reg_num)}), {self.ranges}, {self.use_positions})"
            return f"Fixed({self.reg_num}({LIR_FloatReg(self.reg_num)}), {self.ranges}, {self.use_positions})"
        if 0 <= self.assigned_reg < LIR_Opr.n_phyregs:
            s = f'(in {self.assigned_reg})'
        elif LIR_Opr.n_phyregs <= self.assigned_reg:
            s = f'(in stackslot: {self.assigned_reg - LIR_Opr.n_phyregs})'
        else:
            s = '(unassigned)'
        match self.type:
            case BasicType.T_INT:
                return f"SplitParent({self.reg_num}{s}, INT, {self.ranges}, {self.use_positions})"
            case BasicType.T_FLOAT:
                return f"SplitParent({self.reg_num}{s}, FLOAT, {self.ranges}, {self.use_positions})"



@final
class SplitChild(Interval):
    def __init__(self, reg: LIR_VirtualReg, /, parent: SplitParent):
        super().__init__(reg.reg_num, parent.type)
        assert parent.reg_num != reg.reg_num
        self.__vreg = reg
        self.__insert_move_when_activated = False
        self.__split_parent = parent
        self.set_register_hint(parent)
        parent.split_children.append(self)

    @property
    def insert_move_when_activated(self):
        return self.__insert_move_when_activated
    
    def set_insert_move_when_activated(self):
        self.__insert_move_when_activated = True

    @property
    def split_parent(self):
        return self.__split_parent
    
    @property
    def current_split_child(self):
        return self.__split_parent.current_split_child
    
    def make_current_split_child(self):
        self.__split_parent.make_current_split_child(self)
    
    @property
    def canonical_spill_slot(self):
        return self.__split_parent.canonical_spill_slot
    
    @canonical_spill_slot.setter
    def canonical_spill_slot(self, value: int):
        self.__split_parent.canonical_spill_slot = value

    @property
    def spill_state(self):
        return self.__split_parent.spill_state
    
    @spill_state.setter
    def spill_state(self, state: IntervalSpillState):
        self.__split_parent.spill_state = state

    @property
    def spill_definition_pos(self):
        return self.__split_parent.spill_definition_pos
    
    @spill_definition_pos.setter
    def spill_definition_pos(self, value: int):
        self.__split_parent.spill_definition_pos = value

    def __repr__(self):
        if 0 <= self.assigned_reg < LIR_Opr.n_phyregs:
            s = f'(in {self.assigned_reg})'
        elif LIR_Opr.n_phyregs <= self.assigned_reg:
            s = f'(in stackslot: {self.assigned_reg - LIR_Opr.n_phyregs})'
        else:
            s = '(unassigned)'
        match self.type:
            case BasicType.T_INT:
                return f"SplitChild({self.reg_num}{s}, INT, {self.ranges}, {self.use_positions})"
            case BasicType.T_FLOAT:
                return f"SplitChild({self.reg_num}{s}, FLOAT, {self.ranges}, {self.use_positions})"

