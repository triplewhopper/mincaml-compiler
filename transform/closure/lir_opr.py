from transform.closure.basictype import BasicType
from typing import TypeAlias, TypeGuard, Final
from transform.closure.label import Label
import transform.closure.hir as hir


class LIR_Opr:
    vreg_base: Final = 100
    n_cpu_regs: Final = 32
    n_float_regs: Final = 32
    n_phyregs: Final = n_cpu_regs + n_float_regs

    @property
    def basic_type(self) -> BasicType: raise NotImplementedError()


class LIR_Const(LIR_Opr):

    def __init__(self, c: 'hir.Constant', /):
        self.value = c.value

    def __repr__(self) -> str:
        if isinstance(self.value, int):
            return f'[int:{self.value}|I]'
        return f'[float:{repr(self.value)}|F]'
    
    def __eq__(self, __value: object) -> bool:
        return isinstance(__value, LIR_Const) and self.value == __value.value
    
    def __hash__(self) -> int:
        return hash((LIR_Const, self.value))

    @property
    def basic_type(self):
        return (BasicType.T_INT, BasicType.T_FLOAT)[isinstance(self.value, float)]


class LIR_VirtualReg(LIR_Opr):
    __slots__ = 'reg_num', '__basic_type'
    __reg_count = LIR_Opr.vreg_base

    @classmethod
    def reset(cls):
        cls.__reg_count = cls.vreg_base

    def __init__(self, basic_type: BasicType, /):
        self.__basic_type = basic_type
        self.reg_num = LIR_VirtualReg.__reg_count
        LIR_VirtualReg.__reg_count += 1

    def __repr__(self) -> str:
        match self.basic_type:
            case BasicType.T_INT: return f'[R{self.reg_num}|I]'
            case BasicType.T_FLOAT: return f'[R{self.reg_num}|F]'

    def __eq__(self, __value: object) -> bool:
        return isinstance(__value, LIR_VirtualReg) and self.reg_num == __value.reg_num

    def __hash__(self) -> int:
        return hash(self.reg_num)

    @property
    def basic_type(self): return self.__basic_type

class LIR_PhyReg(LIR_Opr):
    @staticmethod
    def factory(reg_num: int, /) -> 'LIR_CpuReg | LIR_FloatReg':
        if reg_num < LIR_Opr.n_cpu_regs:
            return LIR_CpuReg(reg_num)
        return LIR_FloatReg(reg_num)

class LIR_CpuReg(LIR_PhyReg):
    abi_name = 'zero', 'ra', 'sp', 'gp', 'tp', 't0', 't1', 't2', 's0', 's1', 'a0', 'a1', 'a2', 'a3', 'a4', 'a5', 'a6', 'a7', 's2', 's3', 's4', 's5', 's6', 's7', 's8', 's9', 's10', 's11', 't3', 't4', 't5', 't6'
    caller_saved_names = 'a0', 'a1', 'a2', 'a3', 'a4', 'a5', 'a6', 'a7', 't0', 't1', 't2', 't3', 't4', 't5', 't6'
    callee_saved_names = 's0', 's1', 's2', 's3', 's4', 's5', 's6', 's7', 's8', 's9', 's10', 's11'
    __pool: dict[int | str, 'LIR_CpuReg']
    __initialized = False

    def __new__(cls, reg_num: int | str):
        if cls.__initialized:
            return cls.__pool[reg_num]

        cls.__pool = {i: super(LIR_CpuReg, cls).__new__(cls) for i in range(32)}
        for k, v in cls.__pool.items(): v.__init__(k)
        cls.__pool.update({cls.abi_name[i]: cls.__pool[i] for i in range(32)})
        cls.__initialized = True
        return cls.__pool[reg_num]

    def __init__(self, reg_num: int | str):
        if isinstance(reg_num, str):
            reg_num = self.abi_name.index(reg_num)
        assert 0 <= reg_num < 32
        self.reg_num = reg_num

    @classmethod
    def caller_saveds(cls):
        return (cls.__pool[i] for i in cls.caller_saved_names)

    @classmethod
    def callee_saveds(cls):
        return (cls.__pool[i] for i in cls.callee_saved_names)

    @property
    def basic_type(self):
        return BasicType.T_INT

    def __eq__(self, __value: object) -> bool:
        return isinstance(__value, LIR_CpuReg) and self.reg_num == __value.reg_num

    def __hash__(self) -> int:
        return hash(self.reg_num)

    def __repr__(self):
        return f'[{LIR_CpuReg.abi_name[self.reg_num]}|I]'
    
    def __str__(self):
        return LIR_CpuReg.abi_name[self.reg_num]


class LIR_FloatReg(LIR_PhyReg):
    abi_name = 'ft0', 'ft1', 'ft2', 'ft3', 'ft4', 'ft5', 'ft6', 'ft7', 'fs0', 'fs1', 'fa0', 'fa1', 'fa2', 'fa3', 'fa4', 'fa5', 'fa6', 'fa7', 'fs2', 'fs3', 'fs4', 'fs5', 'fs6', 'fs7', 'fs8', 'fs9', 'fs10', 'fs11', 'ft8', 'ft9', 'ft10', 'ft11'
    caller_saved_names = 'fa0', 'fa1', 'fa2', 'fa3', 'fa4', 'fa5', 'fa6', 'fa7', 'ft0', 'ft1', 'ft2', 'ft3', 'ft4', 'ft5', 'ft6', 'ft7', 'ft8', 'ft9', 'ft10', 'ft11'
    callee_saved_names = 'fs0', 'fs1', 'fs2', 'fs3', 'fs4', 'fs5', 'fs6', 'fs7', 'fs8', 'fs9', 'fs10', 'fs11'
    __pool: dict[int | str, 'LIR_FloatReg']
    __initialized = False

    def __new__(cls, reg_num: int | str):
        if cls.__initialized:
            return cls.__pool[reg_num]

        cls.__pool = {i: super(LIR_FloatReg, cls).__new__(cls) for i in range(32, 64)}
        for k, v in cls.__pool.items(): v.__init__(k)
        cls.__pool.update({cls.abi_name[i - 32]: cls.__pool[i] for i in range(32, 64)})
        cls.__initialized = True
        return cls.__pool[reg_num]

    def __init__(self, reg_num: int | str):
        if isinstance(reg_num, str):
            reg_num = self.abi_name.index(reg_num) + 32
        assert 32 <= reg_num < 64
        self.reg_num = reg_num

    @classmethod
    def caller_saveds(cls):
        return (cls.__pool[i] for i in cls.caller_saved_names)

    @classmethod
    def callee_saveds(cls):
        return (cls.__pool[i] for i in cls.callee_saved_names)

    @property
    def basic_type(self):
        return BasicType.T_FLOAT

    def __eq__(self, __value: object) -> bool:
        return isinstance(__value, LIR_FloatReg) and self.reg_num == __value.reg_num

    def __hash__(self) -> int:
        return hash(self.reg_num)

    def __repr__(self):
        return f'[{LIR_FloatReg.abi_name[self.reg_num - 32]}|F]'
    
    def __str__(self):
        return LIR_FloatReg.abi_name[self.reg_num - 32]
    
_ = LIR_CpuReg(0)
_ = LIR_FloatReg(32)


class LIR_StackSlot(LIR_Opr):
    def __init__(self, stack_word_offset: int, basic_type: BasicType):
        self.stack_word_offset = stack_word_offset
        self.__basic_type = basic_type

    @property
    def basic_type(self): return self.__basic_type

    def __repr__(self) -> str:
        match self.basic_type:
            case BasicType.T_INT: return f'[stack:{self.stack_word_offset}|I]'
            case BasicType.T_FLOAT: return f'[stack:{self.stack_word_offset}|F]'
    
    # def __str__(self):
    #     if self.stack_word_offset < 0:
    #         return f'{self.stack_word_offset * 4})(sp)'
    #     assert self.stack_word_offset <= LIR_StackSlot.base
    #     return f'{(LIR_StackSlot.base - self.stack_word_offset) * 4}(sp)'


class GlobalVar(LIR_Opr):
    def __init__(self, label: Label, word_offset: int):
        self.label = label
        self.word_offset = word_offset

    @property
    def basic_type(self): return BasicType.T_INT

    def __repr__(self):
        return f'[global:{self.label.label}+{self.word_offset}|I]'


LIR_Reg: TypeAlias = LIR_VirtualReg | LIR_CpuReg | LIR_FloatReg


def is_lir_reg(x: object, /) -> TypeGuard[LIR_Reg]: return isinstance(x, (LIR_VirtualReg, LIR_CpuReg, LIR_FloatReg))


def is_lir_regs(x: tuple[object, ...], /) -> TypeGuard[tuple[LIR_Reg, ...]]: return all(is_lir_reg(i) for i in x)


def is_physical_reg(x: LIR_Opr, /) -> TypeGuard[LIR_CpuReg | LIR_FloatReg]: return isinstance(x, (LIR_CpuReg, LIR_FloatReg))
