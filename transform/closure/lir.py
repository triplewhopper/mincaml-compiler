from enum import Enum, auto
from typing import Sequence, LiteralString, TypeAlias, Final
import transform.closure.hir as hir
from transform.closure.basictype import BasicType
from transform.closure.lir_opr import *
from transform.closure.label import Label
from transform.closure.lir_opr import LIR_CpuReg, LIR_FloatReg

CFS: TypeAlias = LIR_CpuReg | LIR_FloatReg | LIR_StackSlot
qemu: Final = False
class LIR_Condition(Enum):
    lir_cond_equal = auto()
    lir_cond_notEqual = auto()
    lir_cond_less = auto()
    lir_cond_lessEqual = auto()
    lir_cond_greaterEqual = auto()
    lir_cond_greater = auto()
    lir_cond_always = auto()

    def __repr__(self) -> str:
        return {
            LIR_Condition.lir_cond_equal: 'EQ',
            LIR_Condition.lir_cond_notEqual: 'NE',
            LIR_Condition.lir_cond_less: 'LT',
            LIR_Condition.lir_cond_lessEqual: 'LE',
            LIR_Condition.lir_cond_greaterEqual: 'GE',
            LIR_Condition.lir_cond_greater: 'GT',
            LIR_Condition.lir_cond_always: 'AL'
        }[self]

# class LIR_MoveKind(Enum):
#     lir_move_normal = auto()
#     lir_move_wide = auto()


class LIR_Op:

    is_call: bool = False
    def __init__(self, result: LIR_Reg | None):
        self._result = result
        self._source: hir.Instruction | None = None
        self._id = -1

    def input_oprs(self) -> Sequence['LIR_Reg']: return ()
    # def input_opr_use_kinds(self) -> Sequence[LiteralString]: return ()
    def tmp_oprs(self) -> Sequence['LIR_Reg']: return ()
    def output_oprs(self) -> Sequence['LIR_Reg']: 
        if self.result is not None:
            return self.result,
        return ()
    
    # @classmethod
    # @abstractmethod
    # def set_input_oprs(self, *oprs: CFS) -> "LIR_Op":
    #     return self
    
    # # @classmethod
    # @abstractmethod
    # def set_tmp_oprs(self, *oprs: CFS) -> "LIR_Op":
    #     return self

    # # @classmethod
    # @abstractmethod
    # def set_output_oprs(self, *oprs: CFS) -> "LIR_Op":
    #     return self
    
    @property
    def id(self): return self._id
    @id.setter
    def id(self, id: int): self._id = id
    @property
    def result(self): return self._result
    @result.setter
    def result(self, result: LIR_Reg): self._result = result
    @property
    def source(self): return self._source
    @source.setter
    def source(self, source: 'hir.Instruction'): 
        assert self._source is None
        self._source = source

class LIR_OpLabel(LIR_Op):
    def __init__(self, lbl: Label):
        super().__init__(None)
        self.__label = lbl
    def set_input_oprs(self, *oprs: CFS): return self
    def set_tmp_oprs(self, *oprs: CFS): return self
    def set_output_oprs(self, *oprs: CFS): return self
    @property
    def label(self): return self.__label
    def __repr__(self):
        return f'label {self.label!r}'

class LIR_Op0(LIR_Op):
    def __init__(self, result: LIR_Reg | None):
        super().__init__(result)

class LIR_Op1(LIR_Op):
    def __init__(self, opr: LIR_Reg, result: LIR_Reg | None):
        super().__init__(result)
        self.__opr = opr
    @property
    def opr(self): return self.__opr
    def input_oprs(self): return self.__opr,
    @opr.setter
    def opr(self, opr: LIR_Reg): self.__opr = opr

class LIR_OpLoadFloatImm(LIR_Op0):
    def __init__(self, imm: float, result: LIR_Reg):
        assert result.basic_type is BasicType.T_FLOAT
        super().__init__(result)
        self.__imm = imm
        self.__tmp = None if imm == 0.0 else LIR_VirtualReg(BasicType.T_INT)

    @property
    def imm(self): return self.__imm
    @property
    def tmp(self): return self.__tmp
    def tmp_oprs(self): return () if self.__tmp is None else (self.__tmp,)
    def set_tmp_oprs(self, *oprs: CFS):
        o = oprs[0]
        assert isinstance(o, LIR_PhyReg)
        self.__tmp = o
        return self
    def __repr__(self) -> str:
        return f'{self.result!r} = load {self.imm}' + (f' (tmp={self.tmp!r})' if self.tmp is not None else '')

class LIR_OpMove(LIR_Op):
    def __init__(self, opr: LIR_Reg | LIR_Const, result: LIR_Reg):
        if isinstance(opr, LIR_Const):
            assert result.basic_type is BasicType.T_INT
        assert opr.basic_type == result.basic_type
        super().__init__(result)
        self.opr = opr

    def input_oprs(self): return (self.opr,) if isinstance(self.opr, LIR_Reg) else ()
    def __repr__(self) -> str:
        return f'{self.result!r} = move {self.opr!r}'
    
class LIR_OpLoadZero(LIR_Op0):
    def __init__(self, result: LIR_Reg):
        assert result.basic_type is BasicType.T_INT
        super().__init__(result)
    def __repr__(self) -> str:
        return f'{self.result!r} = 0'

class LIR_OpLoadWord(LIR_Op1):
    def __init__(self, base_opr: LIR_Reg, word_offset: int, result: LIR_Reg):
        assert base_opr.basic_type is BasicType.T_INT
        super().__init__(base_opr, result)
        self.__offset = word_offset
    @property
    def offset(self): return self.__offset
    def __repr__(self) -> str:
        return f'{self.result!r} = load from {self.opr!r} (disp:{self.offset * 4:+} bytes)'

class LIR_OpRestore(LIR_Op):
    def __init__(self, opr: LIR_StackSlot, result: LIR_Reg):
        assert opr.basic_type == result.basic_type
        super().__init__(result)
        self.__opr = opr
    @property
    def opr(self): return self.__opr
    def __repr__(self) -> str:
        return f'{self.result!r} = restore {self.opr!r}'

class LIR_OpConvert(LIR_Op1):
    def __init__(self, opr: LIR_Reg, result: LIR_Reg):
        assert opr.basic_type != result.basic_type
        super().__init__(opr, result)

    def input_oprs(self): return self.opr,
    def __repr__(self) -> str:
        return f'convert {self.opr!r} to {self.result!r}'

class LIR_OpSpill(LIR_Op1):
    def __init__(self, opr: LIR_Reg, stack_slot: LIR_StackSlot):
        assert opr.basic_type == stack_slot.basic_type
        super().__init__(opr, None)
        self.__stack_slot = stack_slot

    @property
    def stack_slot(self): return self.__stack_slot
    def __repr__(self) -> str:
        return f'spill {self.opr!r} to {self.__stack_slot!r}'

class LIR_OpReturn(LIR_Op):
    def __init__(self, oprs: Sequence[LIR_Reg]):
        super().__init__(None)
        self.__oprs = tuple(oprs)
    def input_oprs(self): return self.__oprs
    def __repr__(self):
        return 'return ' + ', '.join(map(str, self.__oprs))

class LIR_OpGoto(LIR_Op0):
    def __init__(self, target: 'hir.BlockBegin'):
        super().__init__(None)
        self.__target = target
    @property
    def target(self): return self.__target
    def __repr__(self):
        return f'goto {self.target}'


class LIR_Op2(LIR_Op):
    def __init__(self, opr1: LIR_Reg, opr2: LIR_Reg, result: LIR_Reg | None):
        super().__init__(result)
        self.__opr1, self.__opr2 = opr1, opr2
    @property
    def opr1(self): return self.__opr1
    @property
    def opr2(self): return self.__opr2
    def input_oprs(self): return self.opr1, self.opr2

class LIR_OpStoreWord(LIR_Op2):
    def __init__(self, value: LIR_Reg, base_opr: LIR_Reg, word_offset: int):
        assert base_opr.basic_type is BasicType.T_INT
        super().__init__(value, base_opr, None)
        self.__offset = word_offset
    @property
    def offset(self): return self.__offset
    def __repr__(self) -> str:
        return f'store {self.opr1!r} to {self.opr2!r} (disp:{self.offset * 4:+} bytes)'

class LIR_OpStoreWordGlobal(LIR_Op1):
    def __init__(self, value: LIR_Reg, global_var: GlobalVar):
        assert value.basic_type is BasicType.T_INT
        super().__init__(value, None)
        self.__tmp = LIR_VirtualReg(BasicType.T_INT)
        self.__global_var = global_var

    @property
    def global_var(self): return self.__global_var
    @property
    def tmp(self): return self.__tmp
    def tmp_oprs(self): return self.__tmp,

    def __repr__(self) -> str:
        return f'store {self.opr!r} (tmp={self.tmp!r}) to {self.global_var}'

class LIR_OpLoadWordGlobal(LIR_Op0):
    def __init__(self, global_var: GlobalVar, result: LIR_Reg):
        super().__init__(result)
        self.__global_var = global_var
        self.__tmp = LIR_VirtualReg(BasicType.T_INT)

    @property
    def global_var(self): return self.__global_var
    @property
    def tmp(self): return self.__tmp
    def tmp_oprs(self): return self.__tmp,

    def __repr__(self) -> str:
        return f'{self.result!r} = load {self.global_var} (tmp={self.tmp!r})'
    
class LIR_OpBranCond(LIR_Op2):
    op: LiteralString
    def __init__(self, opr1: LIR_Reg, opr2: LIR_Reg, target: 'hir.BlockBegin'):
        super().__init__(opr1, opr2, None)
        self.__target = target
    @property
    def target(self): return self.__target

    def __repr__(self) -> str:
        return f'{self.op} {self.opr1!r} {self.opr2!r} {self.target}'

class LIR_OpBeq(LIR_OpBranCond): op = 'beq'
class LIR_OpBne(LIR_OpBranCond): op = 'bne'
class LIR_OpBlt(LIR_OpBranCond): op = 'blt'
class LIR_OpBge(LIR_OpBranCond): op = 'bge'

class LIR_OpArithImm(LIR_Op1):
    op: LiteralString
    def __init__(self, opr: LIR_Reg, imm: int, result: LIR_Reg):
        assert opr.basic_type is result.basic_type is BasicType.T_INT
        super().__init__(opr, result)
        self.__imm = imm

    @property
    def imm(self): return self.__imm
    def __repr__(self) -> str:
        return f'{self.result!r} = {self.op} {self.opr!r} {self.imm}'

class LIR_OpSlli(LIR_OpArithImm): op = 'slli'
class LIR_OpAddi(LIR_OpArithImm): op = 'addi'
class LIR_OpSrai(LIR_OpArithImm): op = 'srai'

class LIR_OpArith(LIR_Op2):
    op: LiteralString
    def __init__(self, opr1: LIR_Reg, opr2: LIR_Reg, result: LIR_Reg):
        assert opr1.basic_type is opr2.basic_type is result.basic_type is BasicType.T_INT
        super().__init__(opr1, opr2, result)
    def __repr__(self) -> str:
        return f'{self.result!r} = {self.op} {self.opr1!r} {self.opr2!r}'

class LIR_OpAdd(LIR_OpArith): op = 'add'
class LIR_OpSub(LIR_OpArith): op = 'sub'
class LIR_OpXor(LIR_OpArith): op = 'xor'

class LIR_OpFloatArith(LIR_Op2):
    op: LiteralString
    def __repr__(self) -> str:
        return f'{self.result!r} = {self.op} {self.opr1!r} {self.opr2!r}'
    
class LIR_OpFAdd(LIR_OpFloatArith): op = 'fadd.s'
class LIR_OpFSub(LIR_OpFloatArith): op = 'fsub.s'
class LIR_OpFMul(LIR_OpFloatArith): op = 'fmul.s'
class LIR_OpFDiv(LIR_OpFloatArith): op = 'fdiv.s'

class LIR_OpFloatCmp(LIR_Op2):
    op: LiteralString
    def __init__(self, opr1: LIR_Reg, opr2: LIR_Reg, result: LIR_Reg):
        assert opr1.basic_type is opr2.basic_type is BasicType.T_FLOAT and result.basic_type is BasicType.T_INT
        super().__init__(opr1, opr2, result)
    def __repr__(self) -> str:
        return f'{self.result!r} = {self.op} {self.opr1!r} {self.opr2!r}'

class LIR_OpFeq(LIR_OpFloatCmp): op = 'feq.s'
class LIR_OpFlt(LIR_OpFloatCmp): op = 'flt.s'
class LIR_OpFle(LIR_OpFloatCmp): op = 'fle.s'

class LIR_OpCmp(LIR_Op2):
    op: LiteralString

    def __init__(self, opr1: LIR_Reg, opr2: LIR_Reg, result: LIR_Reg):
        assert opr1.basic_type is opr2.basic_type is result.basic_type is BasicType.T_INT
        super().__init__(opr1, opr2, result)

    def __repr__(self) -> str:
        return f'{self.result!r} = {self.op} {self.opr1!r} {self.opr2!r}'

class LIR_OpSlt(LIR_OpCmp): op = 'slt'

class LIR_OpUnary(LIR_Op1):
    op: LiteralString
    basic_types: tuple[BasicType, BasicType]
    _ff = BasicType.T_FLOAT, BasicType.T_FLOAT
    _ii = BasicType.T_INT, BasicType.T_INT
    def __init__(self, opr: LIR_Reg, result: LIR_Reg):
        assert opr.basic_type == self.basic_types[0] and result.basic_type == self.basic_types[1]
        super().__init__(opr, result)
    def __repr__(self) -> str:
        return f'{self.result!r} = {self.op} {self.opr!r} '

class LIR_OpSeqz(LIR_OpUnary): op = 'seqz'; basic_types = LIR_OpUnary._ii
class LIR_OpSnez(LIR_OpUnary): op = 'snez'; basic_types = LIR_OpUnary._ii
class LIR_OpNeg(LIR_OpUnary): op = 'neg'; basic_types = LIR_OpUnary._ii
class LIR_OpFNeg(LIR_OpUnary): op = 'fneg.s'; basic_types = LIR_OpUnary._ff
class LIR_OpFSqrt(LIR_OpUnary): op = 'fsqrt.s'; basic_types = LIR_OpUnary._ff
class LIR_OpFAbs(LIR_OpUnary): op = 'fabs.s'; basic_types = LIR_OpUnary._ff
class LIR_OpFSin(LIR_OpUnary): op = 'mincaml_sin'; basic_types = LIR_OpUnary._ff; is_call = True
class LIR_OpFCos(LIR_OpUnary): op = 'mincaml_cos'; basic_types = LIR_OpUnary._ff; is_call = True
class LIR_OpFFloor(LIR_OpUnary): op = 'mincaml_floor'; basic_types = LIR_OpUnary._ff; is_call = True
class LIR_OpFAtan(LIR_OpUnary): op = 'mincaml_atan'; basic_types = LIR_OpUnary._ff; is_call = True

class LIR_OpCall(LIR_Op):
    is_call = True

    def __init__(self, callee: 'hir.Function', args: Sequence[LIR_Reg], tail: bool, results: Sequence[LIR_Reg]):
        super().__init__(None)
        self.__callee = callee
        self.__args = tuple(args)
        self.__results = tuple(results)
        self.__tail = tail
    @property
    def callee(self): return self.__callee
    @property
    def args(self): return self.__args
    @property
    def results(self): return self.__results
    def input_oprs(self): return self.args
    def output_oprs(self): return self.__results
    def __repr__(self) -> str:
        if self.results:
            return f'{self.results} = {"tail " if self.__tail else ""}call {self.callee} {self.args}'

        return f'{"tail " if self.__tail else ""}call {self.callee} {self.args}'
    
class LIR_Op3(LIR_Op):
    def __init__(self, opr1: LIR_Reg, opr2: LIR_Reg, opr3: LIR_Reg, result: LIR_Reg | None):
        super().__init__(result)
        self.__opr1, self.__opr2, self.__opr3 = opr1, opr2, opr3
    @property
    def opr1(self): return self.__opr1
    @property
    def opr2(self): return self.__opr2
    @property
    def opr3(self): return self.__opr3
    def input_oprs(self): return self.opr1, self.opr2, self.opr3

class LIR_OpAllocArray(LIR_Op):
    is_call = True
    def __init__(self, size: LIR_Reg, inits: Sequence[LIR_Reg], result: LIR_Reg, on_stack_res_length: int):
        assert size.basic_type is result.basic_type is BasicType.T_INT
        super().__init__(result)
        self.__size = size
        self.__inits = tuple(inits)
        self.on_stack_res_length = on_stack_res_length
    @property
    def size(self): return self.__size
    @property
    def inits(self): return self.__inits
    def __repr__(self) -> str:
        return f'{self.result!r} = alloc_array {self.__size!r} {self.__inits!r}'

class LIR_OpReadInt(LIR_Op0):
    is_call = qemu
    def __init__(self, result: LIR_Reg):
        assert result.basic_type is BasicType.T_INT
        super().__init__(result)
    def __repr__(self) -> str:
        return f'{self.result!r} = read_int'

class LIR_OpReadFloat(LIR_Op0):
    is_call = qemu
    def __init__(self, result: LIR_Reg):
        assert result.basic_type is BasicType.T_FLOAT
        super().__init__(result)
    def __repr__(self) -> str:
        return f'{self.result!r} = read_float'

class LIR_OpPrintInt(LIR_Op1):
    is_call = True
    def __init__(self, value: LIR_Reg):
        assert value.basic_type is BasicType.T_INT
        super().__init__(value, None)
    def __repr__(self) -> str:
        return f'print_int {self.opr!r}'
    
class LIR_OpPrintByte(LIR_Op1):
    is_call = qemu
    def __init__(self, value: LIR_Reg):
        assert value.basic_type is BasicType.T_INT
        super().__init__(value, None)
    def __repr__(self) -> str:
        return f'out {self.opr!r}'

class LIR_OpComment(LIR_Op0):
    def __init__(self, comment: str):
        super().__init__(None)
        self.__comment = comment
    @property
    def comment(self): return self.__comment
    def __repr__(self) -> str:
        return f'# {self.comment}'
