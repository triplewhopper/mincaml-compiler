from opkinds import BinaryOpKind
from collections import ChainMap
from typing import overload, Literal, Callable, TypeVar
from transform.closure.basictype import BasicType
from transform.closure.hir import *
from transform.closure.lir import *
from logging import getLogger
from collections import deque
logger = getLogger(__name__)

def vfreg():
    return LIR_VirtualReg(BasicType.T_FLOAT)


def vreg():
    return LIR_VirtualReg(BasicType.T_INT)


T = TypeVar('T', bound='Instruction')
S = TypeVar('S', bound='LIRList')


def memo(f: Callable[[S, T], tuple[LIR_Reg, ...]]) -> Callable[[S, T], tuple[LIR_Reg, ...]]:
    def wrapper(self: S, x: T, /):
        if x.id in self.env:
            return self.env[x.id]
        res = f(self, x)
        self.env[x.id] = res
        return res

    return wrapper

def decompose(n: int):
    powers: list[int] = []
    while n > 0:
        powers.append((n & -n).bit_length() - 1)
        n = n & (n - 1)
    return powers


class LIRList:
    def __init__(self, block: 'BlockBegin'):
        self.__block = block
        self.__lir: list[LIR_Op] = []
        self.__patch_moves: list[LIR_OpMove] = []
        self.__is_finished = False
        self.__callee_saveds: Sequence[LIR_VirtualReg] = []
        self.env: ChainMap[int, tuple[LIR_Reg, ...]] = ChainMap()
        self.__deleted = False

    def reset(self):
        assert self.__block.is_entry
        LIR_VirtualReg.reset() # this relates to assigning new reg_num for split child in linear scan
        self.__lir.clear()
        self.__patch_moves.clear()
        self.__is_finished = False
        self.env = ChainMap()
    
    @property
    def is_finished(self):
        return self.__is_finished
    
    @property
    def is_entry(self):
        return self.__block.is_entry
    
    @property
    def block(self):
        return self.__block
    
    @property
    def deleted(self):
        return self.__deleted
    
    @deleted.setter
    def deleted(self, value: Literal[True]):
        self.__deleted = value
    
    @is_finished.setter
    def is_finished(self, value: Literal[True]):
        self.__is_finished = value

    @property
    def patch_moves(self):
        return tuple(self.__patch_moves)
    
    @property
    def lir(self):
        if self.__patch_moves:
            assert len(self.__block.end.sux) == 1
        return self.__lir

    @overload
    def append(self, op: LIR_Op, /, none_result: Literal[False] = False) -> LIR_Reg:
        ...

    @overload
    def append(self, op: LIR_Op, /, none_result: Literal[True]) -> None:
        ...

    def append(self, op: LIR_Op, /, none_result: bool = False):
        if not self.is_finished:
            self.__lir.append(op)
        else:
            assert len(self.__block.end.sux) == 1 # it is obviously illegal to insert a new op before end of block when the block has multiple successors
            assert not isinstance(op, (LIR_OpLabel, LIR_OpGoto, LIR_OpReturn, LIR_OpCall, LIR_OpBranCond))
            self.__lir.insert(-1, op)
        assert none_result and op.result is None or not none_result and op.result is not None
        return op.result

    def insert_patch_move(self, x: LIR_OpMove):
        assert len(self.__block.end.sux) == 1
        self.__patch_moves.append(x)
        if x.result is not None:
            assert x.result not in self.env
        return x.result

    @overload
    def lookup(self, v: 'Value', allow_int_constant: Literal[False] = False) -> tuple[LIR_Reg, ...]:
        ...

    @overload
    def lookup(self, v: 'Value', allow_int_constant: Literal[True]) -> tuple[LIR_Reg, ...] | tuple['Constant']:
        ...

    def lookup(self, v: 'Value', allow_int_constant: bool = False):
        if isinstance(v, Constant):
            if isinstance(v.type, FloatType):
                return self.float_constant(v)
            elif allow_int_constant:
                return v,
            return self.int_constant(v)
        try:
            res = self.env[v.id]
        except KeyError:
            res = self.dispatch(v)
            self.env[v.id] = res
        assert is_lir_regs(res)
        return res

    def dispatch(self, v: 'Value') -> tuple[LIR_Reg, ...]:
        match v:
            case ArithmeticOp():
                return self.arithmetic_op(v)
            case NegateOp():
                return self.negate_op(v)
            case Convert():
                return self.convert(v)
            case IfOp():
                return self.if_op(v)
            case LogicOp():
                return self.logic_op(v)
            case CompareOp():
                return self.compare_op(v)
            case NewTuple():
                return self.new_tuple(v)
            case LoadField():
                return self.load_field(v)
            case Local():
                return self.local(v)
            case Phi():
                return self.phi(v)
            case NewArray():
                return self.new_array(v)
            case FloatPrimitive():
                return self.float_primitives(v)
            case _:
                raise ValueError(v)

    @memo
    def int_constant(self, c: 'Constant'):
        assert isinstance(c.value, int)
        if c.value == 0:
            return LIR_CpuReg(0),
        return self.move(LIR_Const(c), vreg()),

    @memo
    def float_constant(self, c: 'Constant'):
        assert isinstance(c.value, float)
        return self.append(LIR_OpLoadFloatImm(c.value, vfreg())),

    def move(self, x: 'LIR_Reg | LIR_Const | Constant', y: LIR_Reg, patch: bool = False):
        if isinstance(x, Constant):
            lir_op = LIR_OpMove(LIR_Const(x), y)
        else:
            lir_op = LIR_OpMove(x, y)

        if not patch:
            return self.append(lir_op)
        res = self.insert_patch_move(lir_op)
        assert res is not None
        return res

    def add(self, x: LIR_Reg, y: 'LIR_Reg | Constant', minus: bool = False):
        if isinstance(y, LIR_Reg):
            return self.append(LIR_OpAdd(x, y, vreg()))
        imm = y.value
        if minus: imm = -imm
        assert isinstance(imm, int)
        if -2048 <= imm <= 2047:
            return self.append(LIR_OpAddi(x, imm, vreg()))
        else:
            y1 = self.move(LIR_Const(y), vreg())
            return self.append(LIR_OpAdd(x, y1, vreg()))

    def sub(self, x: LIR_Reg, y: 'LIR_Reg | Constant'):
        if isinstance(y, Constant):
            return self.add(x, y, minus=True)
        return self.append(LIR_OpSub(x, y, vreg()))

    def fadd(self, x: LIR_Reg, y: LIR_Reg):
        return self.append(LIR_OpFAdd(x, y, vfreg()))

    def fsub(self, x: LIR_Reg, y: LIR_Reg):
        return self.append(LIR_OpFSub(x, y, vfreg()))

    def fmul(self, x: LIR_Reg, y: LIR_Reg):
        return self.append(LIR_OpFMul(x, y, vfreg()))

    def fdiv(self, x: LIR_Reg, y: LIR_Reg):
        return self.append(LIR_OpFDiv(x, y, vfreg()))

    def shift_left(self, x: LIR_Reg, y: int):
        return self.append(LIR_OpSlli(x, y, vreg()))

    def shift_right(self, x: LIR_Reg, y: int):
        return self.append(LIR_OpSrai(x, y, vreg()))

    @memo
    def arithmetic_op(self, x: 'ArithmeticOp'):
        opr1, = self.lookup(x.x)
        match x.op:
            case BinaryOpKind.I_ADD:
                opr2, = self.lookup(x.y, True)
                res = self.add(opr1, opr2)
            case BinaryOpKind.I_SUB:
                opr2, = self.lookup(x.y, True)
                res = self.sub(opr1, opr2)
            case BinaryOpKind.I_MUL | BinaryOpKind.I_DIV:
                opr2, = self.lookup(x.y, True)
                if not isinstance(opr2, Constant):
                    raise NotImplementedError(x.op)
                v = opr2.value
                assert isinstance(v, int)
                if v & (v - 1) != 0:
                    raise NotImplementedError(x.op)
                if x.op == BinaryOpKind.I_DIV:
                    res = self.shift_right(opr1, v.bit_length() - 1)
                else:
                    res = self.shift_left(opr1, v.bit_length() - 1)
            case BinaryOpKind.F_ADD:
                opr2, = self.lookup(x.y)
                res = self.fadd(opr1, opr2)
            case BinaryOpKind.F_SUB:
                opr2, = self.lookup(x.y)
                res = self.fsub(opr1, opr2)
            case BinaryOpKind.F_MUL:
                opr2, = self.lookup(x.y)
                res = self.fmul(opr1, opr2)
            case BinaryOpKind.F_DIV:
                opr2, = self.lookup(x.y)
                res = self.fdiv(opr1, opr2)
            case _:
                raise ValueError(x.op)
        return res,

    @memo
    def negate_op(self, x: 'NegateOp'):
        opr, = self.lookup(x.x)
        match x.type:
            case IntType():
                return self.append(LIR_OpNeg(opr, vreg())),
            case FloatType():
                return self.append(LIR_OpFNeg(opr, vfreg())),
            case _:
                raise ValueError(x.type)

    @memo
    def convert(self, x: 'Convert'):
        match x.type:
            case IntType():
                dst = vreg()
            case FloatType():
                dst = vfreg()
            case _:
                raise ValueError(x.type)
        opr, = self.lookup(x.value)
        return self.append(LIR_OpConvert(opr, dst)),

    @memo
    def if_op(self, x: 'IfOp') -> tuple[LIR_Reg, ...]:
        match x.cond, x.y.type, x.tval.type, x.fval.type:
            case Condition.EQL, IntConstant(0), IntConstant(1), IntConstant(0):
                opr1, = self.lookup(x.x)
                return self.append(LIR_OpSeqz(opr1, vreg())),
            case _:
                raise NotImplementedError(x)

    def if_(self, x: 'If', /):
        (opr1,), (opr2,) = self.lookup(x.x), self.lookup(x.y)
        match x.cond:
            case Condition.LSS: # not (a < b)  <=>  a >= b  
                f = LIR_OpBge
            case Condition.LEQ: # not (a <= b)  <=>  a > b <=>  b < a
                f = LIR_OpBlt
                opr1, opr2 = opr2, opr1
            case Condition.EQL:
                f = LIR_OpBne
            case Condition.GTR: # not (a > b)  <=>  a <= b  <=>  b >= a
                f = LIR_OpBge
                opr1, opr2 = opr2, opr1
            case Condition.GEQ: # not (a >= b)  <=>  a < b
                f = LIR_OpBlt
            case Condition.NEQ: 
                f = LIR_OpBeq
        self.append(f(opr1, opr2, x.sux[1]), True)
        self.append(LIR_OpGoto(x.sux[0]), True)

    @memo
    def logic_op(self, x: 'LogicOp'):
        (opr1,), (opr2,) = self.lookup(x.x), self.lookup(x.y)
        match x.op:
            case BinaryOpKind.I_AND | BinaryOpKind.I_OR:
                raise NotImplementedError(x.op)
            case BinaryOpKind.I_XOR:
                res = self.append(LIR_OpXor(opr1, opr2, vreg()))
            case _:
                raise ValueError(x.op)
        return res,

    @memo
    def compare_op(self, x: 'CompareOp'):
        (opr1,), (opr2,) = self.lookup(x.x), self.lookup(x.y)
        match x.op:
            case BinaryOpKind.F_LT:
                f = LIR_OpFlt
            case BinaryOpKind.F_LE:
                f = LIR_OpFle
            case BinaryOpKind.F_EQ:
                f = LIR_OpFeq
            case BinaryOpKind.F_GT:
                f = LIR_OpFlt
                opr2, opr1 = opr1, opr2
            case BinaryOpKind.F_GE:
                f = LIR_OpFle
                opr2, opr1 = opr1, opr2
            case BinaryOpKind.F_NEQ:
                f = LIR_OpFeq
            case _:
                raise ValueError(x.op)
        res = self.append(f(opr1, opr2, vreg()))
        if x.op == BinaryOpKind.F_NEQ:
            res = self.append(LIR_OpSeqz(res, vfreg()))
        return res,

    @memo
    def new_tuple(self, x: 'NewTuple'):
        res: list[LIR_Reg] = []
        for y in x.elems:
            res.extend(self.lookup(y))
        return tuple(res)

    @memo
    def load_field(self, x: 'LoadField'):
        regs = self.lookup(x.obj)
        assert x.type is not None
        return regs[x.offset:x.offset + x.type.abi_size]

    @memo
    def load_indexed(self, x: 'LoadIndexed'):
        base, = self.lookup(x.array)
        index, = self.lookup(x.index, True)
        assert x.type is not None

        def load(base: LIR_Reg, word_offset: int, bt: BasicType):
            return self.append(LIR_OpLoadWord(base, word_offset, LIR_VirtualReg(bt)))

        match index:
            case Constant(int(i)):
                regs: list[LIR_Reg] = []
                for j, bt in enumerate(x.type.to_basic_types()):
                    regs.append(load(base, i * x.type.abi_size + j, bt))
                return tuple(regs)
            case _:
                assert is_lir_reg(index)
                if x.type.abi_size.bit_count() == 1:
                    byte_offset = self.append(LIR_OpSlli(index, x.type.abi_size.bit_length() + 1, vreg()))
                    ptr = self.append(LIR_OpAdd(base, byte_offset, vreg()))
                else:

                    self.append(LIR_OpComment(f"array of type {x.type}; index * size {x.type.abi_size}"), True)
                    acc = self.move(LIR_CpuReg(0), vreg())
                    for p in decompose(x.type.abi_size * 4):
                        shifted = self.append(LIR_OpSlli(index, p, vreg()))
                        acc = self.append(LIR_OpAdd(acc, shifted, vreg()))
                    ptr = self.append(LIR_OpAdd(base, acc, vreg()))

                regs: list[LIR_Reg] = []
                for j, bt in enumerate(x.type.to_basic_types()):
                    regs.append(load(ptr, j, bt))
                return tuple(regs)

    def store_indexed(self, x: 'StoreIndexed', /):
        base, = self.lookup(x.array)
        index, = self.lookup(x.index, True)
        assert x.type is None and x.value.type is not None
        regs = self.lookup(x.value)

        def store(value: LIR_Reg, base: LIR_Reg, word_offset: int):
            self.append(LIR_OpStoreWord(value, base, word_offset), True)

        match index:
            case Constant(int(i)):
                for j, reg in enumerate(regs):
                    store(reg, base, i * x.value.type.abi_size + j)
            case _:
                assert is_lir_reg(index)
                if x.value.type.abi_size.bit_count() == 1:
                    byte_offset = self.append(LIR_OpSlli(index, x.value.type.abi_size.bit_length() + 1, vreg()))
                    ptr = self.append(LIR_OpAdd(base, byte_offset, vreg()))
                else:
                    self.append(LIR_OpComment(f"array of type {x.value.type}; index * size {x.value.type.abi_size} in word"), True)
                    acc = self.move(LIR_CpuReg(0), vreg())
                    for p in decompose(x.value.type.abi_size * 4):
                        shifted = self.append(LIR_OpSlli(index, p, vreg()))
                        acc = self.append(LIR_OpAdd(acc, shifted, vreg()))
                    ptr = self.append(LIR_OpAdd(base, acc, vreg()))
                for j, reg in enumerate(regs):
                    store(reg, ptr, j)

    def partition(self, regs: Sequence[LIR_Reg | Constant], n_iregs: int, n_fregs: int):
        a = [LIR_CpuReg(f'a{i}') for i in range(n_iregs)]
        fa = [LIR_FloatReg(f'fa{i}') for i in range(n_fregs)]
        assert all(x not in a and x not in fa for x in regs)
        i, j, k = 0, 0, 0
        iregs, fregs, stack_slots = list[int](), list[int](), list[int]()
        regs_: list[LIR_CpuReg | LIR_FloatReg] = []
        while i + j + k < len(regs):
            if i < len(a) and regs[i + j + k].basic_type is BasicType.T_INT:
                iregs.append(i + j + k)
                regs_.append(a[i])
                i += 1
            elif j < len(fa) and regs[i + j + k].basic_type is BasicType.T_FLOAT:
                fregs.append(i + j + k)
                regs_.append(fa[j])
                j += 1
            else:
                stack_slots.append(i + j + k)
                k += 1
        return iregs, fregs, stack_slots, regs_
    
    def moves(self, srcs: Sequence[LIR_Reg], dsts: Sequence[LIR_Reg]):
        for src, dst in zip(srcs, dsts):
            self.append(LIR_OpMove(src, dst), True)
    
    def pass_arguments(self, args: Sequence[LIR_Reg | Constant], n_iregs: Literal[2, 8], n_fregs: Literal[2, 8], tail: bool):
        iregs, fregs, stack_slots, args_ = self.partition(args, n_iregs, n_fregs)
        constants : list[tuple[Constant, int]] = []
        for n, k in enumerate(stack_slots):
            arg = args[k]
            if isinstance(arg, Constant):
                constants.append((arg, n))
            else:
                if tail: slot = LIR_StackSlot(len(stack_slots) - n - 1, arg.basic_type)
                else: slot = LIR_StackSlot(n - len(stack_slots), arg.basic_type)
                self.append(LIR_OpSpill(arg, slot), none_result=True)
        constants_mem: dict[Constant, LIR_Reg] = {}
        for c, n in constants:
            if c not in constants_mem:
                constants_mem[c] = self.move(LIR_Const(c), LIR_VirtualReg(c.basic_type))
        for c, n in constants:
            if tail: slot = LIR_StackSlot(len(stack_slots) - n - 1, c.basic_type)
            else: slot = LIR_StackSlot(n - len(stack_slots), c.basic_type)
            self.append(LIR_OpSpill(constants_mem[c], slot), none_result=True)

        for n, i in enumerate(iregs): self.move(args[i], LIR_CpuReg(f'a{n}'))
        for n, j in enumerate(fregs): self.move(args[j], LIR_FloatReg(f'fa{n}'))
        return args_
    
    def call_move_res(self, ireg_indices: Sequence[int], freg_indices: Sequence[int], stack_slots: Sequence[int], stack_indices: Sequence[int], results: Sequence[LIR_Reg], /):
        assert len(ireg_indices) + len(freg_indices) + len(stack_indices) == len(results)
        for i, idx in enumerate(ireg_indices):
            self.move(LIR_CpuReg(f'a{i}'), results[idx])
        for j, idx in enumerate(freg_indices):
            self.move(LIR_FloatReg(f'fa{j}'), results[idx])

        for k, idx in zip(stack_slots, stack_indices, strict=True):
            self.append(LIR_OpRestore(LIR_StackSlot(k, results[idx].basic_type),results[idx]))


    def invoke_static(self, x: 'InvokeStatic', /):
        if x.id in self.env:
            return self.env[x.id]
        args = sum((tuple(self.lookup(arg, True)) for arg in x.args), ())
        args_ = self.pass_arguments(args, 8, 8, False)
        if x.type is not None:
            results = tuple(map(LIR_VirtualReg, x.type.to_basic_types()))
            ireg_indices, freg_indices, stack_indices, reg_results_ = self.partition(results, 2, 2)
            self.append(LIR_OpCall(x.receiver, args_, x.tail, reg_results_), True)
            self.call_move_res(ireg_indices, freg_indices, range(-len(stack_indices), 0), stack_indices, results)
            self.env[x.id] = res = tuple(results)
            return res
        else:
            self.append(LIR_OpCall(x.receiver, args_, x.tail, []), True)

    def print_int(self, x: 'PrintInt', /):
        a, = self.lookup(x.arg)
        a0 = LIR_CpuReg('a0')
        self.move(a, a0)
        self.append(LIR_OpPrintInt(a0), True)

    def print_byte(self, x: 'PrintByte', /):
        if not qemu:
            self.append(LIR_OpPrintByte(*self.lookup(x.arg)), True)
        else:
            a, = self.lookup(x.arg)
            a0 = LIR_CpuReg('a0')
            self.move(a, a0)
            self.append(LIR_OpPrintByte(a0), True)

    @memo
    def read_int(self, x: 'ReadInt', /):
        a0 = LIR_CpuReg('a0')
        self.append(LIR_OpReadInt(a0))
        return self.move(a0, vreg()),

    @memo
    def read_float(self, x: 'ReadFloat', /):
        fa0 = LIR_FloatReg('fa0')
        self.append(LIR_OpReadFloat(fa0))
        return self.move(fa0, vfreg()),

    @memo
    def float_primitives(self, x: 'FloatPrimitive', /):
        y, = self.lookup(x.arg)
        match x:
            case Fabs():
                op = LIR_OpFAbs
            case Floor():
                op = LIR_OpFFloor
            case Sin():
                op = LIR_OpFSin
            case Cos():
                op = LIR_OpFCos
            case Sqrt():
                op = LIR_OpFSqrt
            case Atan():
                op = LIR_OpFAtan
            case _:
                raise ValueError(x)
        if not op.is_call:
            return self.append(op(y, vfreg())),
        fa0 = LIR_FloatReg('fa0')
        self.move(y, fa0)
        self.append(op(fa0, fa0))
        return self.move(fa0, vfreg()),

    def store_field(self, x: 'StoreField', /) -> None:
        raise NotImplementedError(x)

    @memo
    def local(self, x: 'Local', /):
        assert x.type is not None
        return tuple(map(LIR_VirtualReg, x.type.to_basic_types()))

    @memo
    def phi(self, x: 'Phi', /):
        assert x.type is not None
        return tuple(map(LIR_VirtualReg, x.type.to_basic_types()))

    @memo
    def new_array(self, x: 'NewArray', /):
        assert x.type is not None
        size, = self.lookup(x.size, True)
        inits = self.lookup(x.init, True)    
        args_ = self.pass_arguments([size, *inits],8, 8, False)
        r = self.append(LIR_OpAllocArray(args_[0], args_[1:], LIR_CpuReg('a0'), len(inits) - len(args_) + 1))
        return self.move(r, vreg()),

    def store_global(self, x: 'StoreGlobal', /):
        values = self.lookup(x.value)
        for i, reg in enumerate(values):
            global_var = GlobalVar(Label(x.name), i)
            self.append(LIR_OpStoreWordGlobal(reg, global_var), True)

    @memo
    def load_global(self, x: 'LoadGlobal', /):
        assert x.type is not None
        regs: list[LIR_Reg] = []
        for i, bt in enumerate(x.type.to_basic_types()):
            global_var = GlobalVar(Label(x.name), i)
            regs.append(self.append(LIR_OpLoadWordGlobal(global_var, LIR_VirtualReg(bt))))
        return tuple(regs)

    def return_(self, x: 'Return', /):
        # for s, d in zip(self.__callee_saveds, chain(LIR_CpuReg.callee_saveds(), LIR_FloatReg.callee_saveds()), strict=True):
        #     self.append(LIR_OpMove(s, d))
        if x.value is not None:
            oprs = self.pass_arguments(self.lookup(x.value, True),2, 2, True)
            self.append(LIR_OpReturn(oprs), True)
        else:
            self.append(LIR_OpReturn(()), True)

    def goto(self, x: 'Goto', /):
        self.append(LIR_OpGoto(x.sux[0]), True)
    
    def gen_patch_moves(self):
        """must be called after gen_lir"""
        assert self.__block.is_entry
        visited = set[int]()
        q = deque([self.__block])
        while q:
            cur = q.popleft()
            assert cur.lir.is_finished
            for succ in cur.end.sux:
                if succ.block_id not in visited:
                    q.append(succ)
                    visited.add(succ.block_id)
            phis: list[Phi] = []
            phi = cur.next
            while isinstance(phi, Phi):
                phis.append(phi)
                phi = phi.next
            if not phis: continue
            for i, prev in enumerate(cur.predesessors):
                assert len(prev.end.sux) == 1, 'critical edge should be removed'
                oprs: list[LIR_Reg | LIR_Const] = []
                for phi in phis:
                    for opr in prev.lir.lookup(phi.preds[i], True):
                        if isinstance(opr, Constant): oprs.append(LIR_Const(opr))
                        else: oprs.append(opr)
                results = list(sum((cur.lir.lookup(phi) for phi in phis), ()))
                assert len(oprs) == len(results)
                for j in reversed(range(len(oprs))):
                    if oprs[j] == results[j]:
                        del oprs[j], results[j]
                blocked = [True] * len(oprs)
                processed = [False] * len(oprs)
                while (i:=next((i for i in range(len(oprs)) if not processed[i] and (results[i] not in oprs or not blocked[oprs.index(results[i])])), None)) is not None:
                    prev.lir.move(oprs[i], results[i], True)
                    blocked[i] = False
                    processed[i] = True

                while (j:=next((j for j in range(len(oprs)) if not processed[j]), None)) is not None:
                    tmp = LIR_VirtualReg(results[j].basic_type)
                    prev.lir.move(oprs[j], tmp, True)
                    blocked[j] = False
                    processed[j] = True
                    while (i:=next((i for i in range(len(oprs)) if not processed[i] and (results[i] not in oprs or not blocked[oprs.index(results[i])])), None)) is not None:
                        prev.lir.move(oprs[i], results[i], True)
                        blocked[i] = False
                        processed[i] = True
                    prev.lir.move(tmp, results[j], True)

                assert all(processed)
    
    def apply_patch_moves(self):
        """must be called after gen_patch_moves"""
        assert self.__block.is_entry
        visited = set[int]()
        q = deque([self.__block])
        while q:
            cur = q.popleft()
            assert cur.lir.is_finished
            for succ in cur.end.sux:
                if succ.block_id not in visited:
                    q.append(succ)
                    visited.add(succ.block_id)
            if cur.lir.__patch_moves:
                cur.lir.__lir[-1:-1] = cur.lir.__patch_moves
                cur.lir.__patch_moves.clear()
        

    def gen_lir(self, prev: 'BlockBegin | Function', visited: set[int], callee_saveds: Sequence[LIR_VirtualReg], /):
        assert isinstance(prev, Function) or prev.block_id in visited
        if self.__block.block_id in visited:
            return
        assert not self.is_finished
        self.append(LIR_OpLabel(Label(Id(f'B{self.__block.block_id}'))), True)
        if isinstance(prev, Function):
            assert self is prev.entry.lir
            assert not callee_saveds
            # _callee_saveds = [vreg() for _ in LIR_CpuReg.callee_saveds()] + [vfreg() for _ in LIR_FloatReg.callee_saveds()]
            # for s, d in zip(chain(LIR_CpuReg.callee_saveds(), LIR_FloatReg.callee_saveds()), _callee_saveds, strict=True):
                # self.append(LIR_OpMove(s, d))
            # self.__callee_saveds = _callee_saveds
            ireg_indices, freg_indices, stackslots, _ = self.partition(prev.formal_arg_vregs, 8, 8)
            self.call_move_res(ireg_indices, freg_indices, range(len(stackslots)-1, -1, -1), stackslots, prev.formal_arg_vregs)
        else:
            self.env = prev.lir.env.new_child()
            self.__callee_saveds = callee_saveds
        visited.add(self.__block.block_id)
        cur = self.__block.next
        while cur is not None:
            match cur:
                case hir.Goto():
                    self.goto(cur)
                case hir.If():
                    self.if_(cur)
                case hir.Return():
                    self.return_(cur)
                case hir.NegateOp():
                    self.negate_op(cur)
                case hir.Phi():
                    self.phi(cur)
                case hir.LoadIndexed():
                    self.load_indexed(cur)
                case hir.StoreIndexed():
                    self.store_indexed(cur)
                case hir.InvokeStatic():
                    self.invoke_static(cur)
                case hir.StoreGlobal():
                    self.store_global(cur)
                case hir.LoadGlobal():
                    self.load_global(cur)
                case hir.ReadInt():
                    self.read_int(cur)
                case hir.ReadFloat():
                    self.read_float(cur)
                case hir.PrintInt():
                    self.print_int(cur)
                case hir.PrintByte():
                    self.print_byte(cur)
                case Constant():
                    ...
                case _:
                    self.dispatch(cur)
            cur = cur.next
        self.is_finished = True
        for succ in self.__block.end.sux:
            succ.lir.gen_lir(self.__block, visited, self.__callee_saveds)

