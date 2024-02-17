from transform.closure.language import Program, Exp, Function, Cls, LetBinding, LitU, LitI, LitB, LitF, Var, Get, Unary, \
    AppCls, AppDir, \
    Binary, Seq, Tuple, Put, If, Let, LetTuple, MakeCls
from ty import Ty, TyFun, TyUnit, TyInt, TyBool, TyFloat, TyTuple, TyArray
from id import Id
from collections import ChainMap
from collections.abc import Mapping, Sequence
from opkinds import BinaryOpKind, UnaryOpKind
from functools import lru_cache
from typing import ClassVar, Callable, LiteralString, Final, TypeGuard, overload, Literal
from dataclasses import dataclass, field, replace
import contextlib

def is_id_list(xs: object) -> TypeGuard[list[Id]]:
    if not isinstance(xs, list):
        return False
    for x in xs: # type: ignore
        if not isinstance(x, Id):
            return False
    return True

@dataclass(slots=True)
class Interval:
    start: int
    end: int

    def __repr__(self):
        if self.start == self.end:
            return '∅'
        return f'[{self.start}, {self.end})'

    def __sub__(self, other: int):
        return Interval(self.start - other, self.end - other)

    def disjoint(self, other: 'Interval', /):
        return self.end <= other.start or other.end <= self.start

    def __bool__(self):
        return self.start != self.end

    @property
    def length(self):
        return self.end - self.start


class FunctionInfo:
    def __init__(self, funct: Id, typ: TyFun):
        self.funct = funct
        self.is_rec = 0
        self.typ = typ
        self.funct_usage = 0
        self.formal_fv: dict[Id, Ty] = {}
        self.formal_args: dict[Id, Ty] = {}
        self.local_vars: dict[Id, Ty] = {}
        self.usage: dict[Id, int] = {}
        self.live_interval: dict[Id, list[Interval]] = {}
        self.pos = Interval(0, 0)

    def __str__(self):
        buf: list[str] = []

        def usage(i: int):
            return f'{i} usage' if i == 1 else f'{i} usages'

        def relative_range(r: list[Interval]):
            return [x - self.pos.start for x in r if x]

        rec = f'rec({self.is_rec}) ' if self.is_rec else ''
        buf.append(f'function {rec}{self.funct} ({usage(self.funct_usage)}): {self.typ}')
        buf.append(f'  range: {self.pos} (length {self.pos.length})')
        buf.append(f"  formal_args:")
        for x, t in self.formal_args.items():
            buf.append(f'    {x!r} {x}: {t}, {usage(self.usage[x])}')
            buf[-1] += ', ' + str(relative_range(self.live_interval[x]))
        if self.formal_fv:
            buf.append(f'  formal_fv:')
            for fv in self.formal_fv:
                buf.append(f"    {fv!r} {fv}: {self.formal_fv[fv]}, {usage(self.usage[fv])}")
                buf[-1] += ', ' + str(relative_range(self.live_interval[fv]))
        buf.append(f'  locals: {len(self.local_vars)}')
        for k in self.local_vars:
            buf.append(f'    {k!r} {k}: {self.local_vars[k]}, {usage(self.usage[k])}')
            buf[-1] += ', ' + str(relative_range(self.live_interval[k]))
        return '\n'.join(buf)


class Count:
    def __init__(self, builtins: dict[Id, Ty]):
        self.env = ChainMap(builtins)
        self.usage = ChainMap({k: 0 for k in self.env.keys()})
        self.live_interval = ChainMap({k: [Interval(0, 0)] for k in self.env})
        self.cur_pos = 0

    def set_globals(self, globals: dict[Id, Ty]):
        self.env = self.env.new_child(globals)
        self.usage = self.usage.new_child({k: 0 for k in globals})
        self.live_interval = self.live_interval.new_child({k: [Interval(0, 0)] for k in globals})
        return self

    @contextlib.contextmanager
    def new_child_env(self, env: dict[Id, Ty]):
        assert self.env.keys().isdisjoint(env.keys())
        self.env = self.env.new_child(env)
        self.usage = self.usage.new_child({k: 0 for k in env})
        self.live_interval = self.live_interval.new_child({k: [Interval(self.cur_pos, self.cur_pos)] for k in env})
        try:
            yield
        finally:
            self.env = self.env.parents
            self.usage = self.usage.parents
            self.live_interval = self.live_interval.parents

    def lookup(self, x: Id):
        self.usage[x] += 1
        self.cur_pos += 1
        self.live_interval[x][-1].end = self.cur_pos
        return self.env[x]

    def count_program(self, prog: Program):
        assert self.env.keys().isdisjoint(f.funct for f in prog.fns)
        with self.new_child_env({f.funct: f.typ for f in prog.fns}):
            function_info: dict[Id, FunctionInfo] = {}
            for f in prog.fns:
                assert len(self.env.maps) == 3
                assert len(self.env.maps[0]) == len(prog.fns)
                assert f.funct not in function_info
                function_info[f.funct] = self.visit_Function(f)

            for e in prog.exp_or_cls_or_letbindings:
                match e:
                    case Exp():
                        self.visit(e)
                    case Cls():
                        self.visit_Cls(e)
                    case LetBinding():
                        self.visit_LetBinding(e)
                        assert e.lhs in self.env

            for f in prog.fns:
                info = function_info[f.funct]
                info.funct_usage = self.usage[f.funct]
                # print(info)
                # print()
            ...

    def visit(self, e: Exp[Ty], /, tail: bool = False) -> None:
        match e:
            case LitU() | LitI() | LitB() | LitF():
                ...
            case Var():
                self.lookup(e.name)
            case Get():
                self.lookup(e.array)
                self.lookup(e.index)
            case Unary():
                self.lookup(e.y)
            case AppCls() | AppDir():
                self.lookup(e.callee)
                for arg in e.args:
                    self.lookup(arg)
            case Binary():
                self.lookup(e.y1)
                self.lookup(e.y2)
            case Seq():
                for e1 in e.es[:-1]:
                    self.visit(e1)
                return self.visit(e.es[-1], tail)
            case Tuple():
                _ = [self.lookup(x) for x in e.ys]
                return e.typ
            case Put():
                array_t = self.lookup(e.array)
                index_t = self.lookup(e.index)
                value_t = self.lookup(e.value)

            case If():
                cond_t = self.lookup(e.cond)
                self.visit(e.br_true, tail)
                self.visit(e.br_false, tail)
                return e.typ
            case Let():
                self.visit(e.binding.rhs)
                assert e.binding.lhs not in self.env
                self.env[e.binding.lhs] = e.binding.rhs.typ
                self.usage[e.binding.lhs] = 0
                self.live_interval[e.binding.lhs] = [Interval(self.cur_pos, self.cur_pos)]
                return self.visit(e.expr, tail)
            case LetTuple():
                assert self.env.keys().isdisjoint(e.xs)
                self.lookup(e.y)
                self.env.update(dict(zip(e.xs, e.ts)))
                self.usage.update({x: 0 for x in e.xs})
                self.live_interval.update({x: [Interval(self.cur_pos, self.cur_pos)] for x in e.xs})
                return self.visit(e.e, tail)

            case MakeCls():
                self.visit_Cls(e.closure)
                return self.visit(e.body, tail)
            case _:
                raise NotImplementedError(e)

    def visit_LetBinding(self, binding: LetBinding):
        rhs_t = self.visit(binding.rhs)
        return rhs_t

    def visit_Cls(self, cls: Cls):
        assert cls.entry.funct in self.env
        for actual_fv, (_, formal_fv_ty) in zip(cls.actual_fv, cls.entry.formal_fv, strict=True):
            assert formal_fv_ty == self.lookup(actual_fv)

    def visit_Function(self, f: Function):
        function_info = FunctionInfo(f.funct, f.typ)
        function_info.pos = Interval(self.cur_pos, self.cur_pos)
        with self.new_child_env(dict(zip(f.formal_args, f.typ.args, strict=True))):
            self.env.update(dict(f.formal_fv))
            self.usage.update({k: 0 for k, _ in f.formal_fv})
            self.live_interval.update({k: [Interval(self.cur_pos, self.cur_pos)] for k, _ in f.formal_fv})
            f_usage0 = self.usage[f.funct]

            self.visit(f.body, tail=True)

            assert f_usage0 <= self.usage[f.funct]

            function_info.pos.end = self.cur_pos
            function_info.is_rec = self.usage[f.funct] - f_usage0
            function_info.formal_args = dict(zip(f.formal_args, f.typ.args))
            function_info.formal_fv = dict(f.formal_fv)
            function_info.local_vars = {k: v for k, v in self.env.maps[0].items() if
                                        k not in f.formal_args and k not in function_info.formal_fv}
            function_info.usage = {k: self.usage[k] for k in self.env.maps[0]}
            function_info.live_interval = {k: self.live_interval[k] for k in self.env.maps[0]}
        return function_info


# def gg(t: TyTuple, prefix: str = ''):
#     res: list[str] = []
#     for i, elem in enumerate(t.elems):
#         match elem:
#             case TyTuple():
#                 res.extend(gg(elem, f'{prefix}:sub_{i}'))
#             case _:
#                 res.append(f'{prefix}:sub_{i}')
#     return res


from typing import NewType


@dataclass(slots=True, frozen=True)
class PhyReg:
    sp: ClassVar['PhyReg']
    gp: ClassVar['PhyReg']
    zero: ClassVar['PhyReg']

    name: str

    def __repr__(self):
        return f'{self.name}'

    def is_float(self):
        return self.name.startswith('f') and self.name != 'fp'
    
    def preserve_on_call(self):
        return self.name in {
            'sp', 's0', 's1', 's2', 's3', 's4', 's5', 's6', 's7', 's8', 's9', 's10', 's11', 
            'gp', 'fs0', 'fs1', 'fs2', 'fs3', 'fs4', 'fs5', 'fs6', 'fs7', 'fs8', 'fs9', 'fs10', 'fs11'}

PhyReg.sp = PhyReg('sp')
PhyReg.gp = PhyReg('gp')
PhyReg.zero = PhyReg('zero')
StackSlot = NewType('StackSlot', int)


class I: ...

@dataclass
class MSimuHalt(I): ...

@dataclass
class MCopy(I):
    is_float: bool
    src: Id | PhyReg
    dst: Id | PhyReg = field(default_factory=Id)

    def __str__(self):
        if self.is_float:
            return f'fmv.s {self.dst!r}, {self.src!r}'
        return f'mv {self.dst!r}, {self.src!r}'


@dataclass
class MLoadImm(I):
    imm: int
    dst: Id | PhyReg = field(default_factory=Id)

    def __str__(self):
        return f'li {self.dst!r}, {self.imm}'


@dataclass
class MLui(I):
    imm: int
    dst: Id | PhyReg = field(default_factory=Id)

    def __str__(self):
        return f'lui {self.dst!r}, {self.imm}'


@dataclass
class MLuiHi(I):
    hi: Id
    dst: Id | PhyReg = field(default_factory=Id)

    def __str__(self):
        return f'lui {self.dst!r}, %hi({self.hi!r})'


@dataclass
class MLoadFZero(I):
    dst: Id | PhyReg = field(default_factory=Id)

    def __str__(self):
        return f'fmv.w.x {self.dst!r}, zero'


@dataclass
class MLoadFloatImm(I):
    float_table: ClassVar[Mapping[float, Id]] = {}
    imm: float
    # addr: Id | PhyReg = field(default_factory=Id)
    dst: Id | PhyReg = field(default_factory=Id)

    def __str__(self):
        l = MLoadFloatImm.float_table[self.imm].dump_as_label()
        return f'flw {self.dst}, %rel_gp({l})(gp) # {self.imm}'
        # return f'lui {self.addr!r}, %hi({l}); flw {self.dst!r}, %lo({l})({self.addr!r}) # {self.imm}'


# @dataclass
# class MLoadGlobalAddr(I):
#     addr: Id
#     dst: Id | PhyReg = field(default_factory=Id)

#     def __str__(self):
#         return f'la {self.dst!r}, {self.addr!r}'

@dataclass
class MOut(I):
    src: Id | PhyReg

    def __str__(self):
        return f'out {self.src!r}'


@dataclass
class MCin(I):
    is_float: bool
    dst: Id | PhyReg = field(default_factory=Id)

    def __str__(self):
        if self.is_float:
            return f'cin_float {self.dst!r}'
        return f'cin_int {self.dst!r}'

@dataclass
class MCout(I):
    is_float: bool
    src: Id | PhyReg

    def __str__(self):
        if self.is_float:
            return f'cout_float {self.src!r}'
        return f'cout_int {self.src!r}'


@dataclass
class MLoad(I):
    is_float: bool
    src: Id | PhyReg
    offset: int
    dst: Id | PhyReg = field(default_factory=Id)

    def __str__(self):
        if self.is_float:
            return f'flw {self.dst!r}, {self.offset}({self.src!r})'
        return f'lw {self.dst!r}, {self.offset}({self.src!r})'


@dataclass
class MLoadLo(I):
    is_float: bool
    src: Id | PhyReg
    lo: Id
    dst: Id | PhyReg = field(default_factory=Id)

    def __str__(self):
        if self.is_float:
            return f'flw {self.dst!r}, %lo({self.lo.dump_as_label()})({self.src!r})'
        return f'lw {self.dst!r}, %lo({self.lo.dump_as_label()})({self.src!r})'


@dataclass
class MStore(I):
    is_float: bool
    val: Id | PhyReg
    ptr: Id | PhyReg
    offset: int

    def __str__(self):
        if self.is_float:
            return f'fsw {self.val!r}, {self.offset}({self.ptr!r})'
        return f'sw {self.val!r}, {self.offset}({self.ptr!r})'


@dataclass
class MStoreLo(I):
    is_float: bool
    val: Id | PhyReg
    ptr: Id | PhyReg
    lo: Id

    def __str__(self):
        if self.is_float:
            return f'fsw {self.val!r}, %lo({self.lo.dump_as_label()})({self.ptr!r})'
        return f'sw {self.val!r}, %lo({self.lo.dump_as_label()})({self.ptr!r})'


@dataclass
class MUnary(I):
    opcode: ClassVar[str]
    is_float: ClassVar[tuple[bool, bool]]
    src: Id | PhyReg
    dst: Id | PhyReg = field(default_factory=Id)

    def __str__(self):
        return f'{self.opcode} {self.dst!r}, {self.src!r}'


@dataclass
class MBinary(I):
    opcode: ClassVar[str]
    is_float: ClassVar[tuple[bool, bool, bool]]
    src1: Id | PhyReg
    src2: Id | PhyReg
    dst: Id | PhyReg = field(default_factory=Id)

    def __str__(self):
        return f'{self.opcode} {self.dst!r}, {self.src1!r}, {self.src2!r}'

@dataclass
class MTernary(I):
    opcode: ClassVar[str]
    is_float: ClassVar[tuple[bool, bool, bool, bool]]
    src1: Id | PhyReg
    src2: Id | PhyReg
    src3: Id | PhyReg
    dst: Id | PhyReg = field(default_factory=Id)

    def __str__(self):
        return f'{self.opcode} {self.dst!r}, {self.src1!r}, {self.src2!r}, {self.src3!r}'

@dataclass
class MFMAdd(MTernary): 
    opcode: ClassVar[str] = 'fmadd.s'
    is_float = True, True, True, True

@dataclass
class MNeg(MUnary): 
    opcode: ClassVar[str] = 'neg'
    is_float = False, False


# @dataclass
# class MNot(MUnary): opcode: ClassVar[str] = 'not'


@dataclass
class MSeqz(MUnary): 
    opcode: ClassVar[str] = 'seqz'
    is_float = False, False


@dataclass
class MSnez(MUnary): 
    opcode: ClassVar[str] = 'snez'
    is_float = False, False


@dataclass
class MFNeg(MUnary): 
    opcode: ClassVar[str] = 'fneg.s'
    is_float = True, True


@dataclass
class MFSqrt(MUnary):
    opcode: ClassVar[str] = 'fsqrt.s'
    is_float = True, True


@dataclass
class MFAbs(MUnary):
    opcode: ClassVar[str] = 'fabs.s'
    is_float = True, True


@dataclass
class MFCvtWS(MUnary):
    opcode: ClassVar[str] = 'fcvt.w.s'
    is_float = True, False


@dataclass
class MFCvtSW(MUnary): 
    opcode: ClassVar[str] = 'fcvt.s.w'
    is_float = False, True


@dataclass
class MFMvWX(MUnary): 
    opcode: ClassVar[str] = 'fmv.w.x'
    is_float = False, True


@dataclass
class MFMvXW(MUnary):
    opcode: ClassVar[str] = 'fmv.x.w'
    is_float = True, False


@dataclass
class MIf(I):
    cond: 'Id | PhyReg | MCmp | MFCmp'
    br_true: I | list[Id | PhyReg]
    br_false: I | list[Id | PhyReg]
    is_float: list[bool]
    dst: list[Id | PhyReg] = field(default_factory=list)

    def __post_init__(self):
        assert len(self.is_float) == len(self.dst)
        match self.br_true, self.br_false:
            case list() as br_true, list() as br_false:
                assert len(br_true) == len(br_false) == len(self.dst)
            case _:
                ...


@dataclass
class MSeq(I):
    instrs: list[I]


@dataclass
class MLabel(I):
    label: Id

    def __str__(self):
        return f'{self.label}:'

    def __repr__(self):
        return f'@{self.label}'


@dataclass
class MJump(I):
    label: MLabel

    def __str__(self):
        return f'j {self.label.label!r}'


# @dataclass
# class Label:
#     dst: Id

#     def __repr__(self):
#         s1, s2 = str(self.dst), repr(self.dst)
#         if s1 != s2:
#             return f'@{s2}(aka {s1})'
#         return f'@{s1}'


@dataclass
class MCall(I):
    callee: 'MFunction'
    args: list[PhyReg | Id]
    args_is_float: list[bool]
    tail: bool
    dsts: list[Id | PhyReg] = field(default_factory=list)
    dsts_is_float: list[bool] = field(default_factory=list)

    def __post_init__(self):
        assert len(self.args) == len(self.args_is_float)
        assert len(self.dsts) == len(self.dsts_is_float)

    def __repr__(self) -> str:
        c1, c2 = str(self.callee.funct), repr(self.callee.funct)
        if c1 != c2:
            return f'MCall({c2}(aka {c1}), args={self.args}, args_is_float={self.args_is_float}, tail={self.tail}, dsts={self.dsts}, dsts_is_float={self.dsts_is_float})'
        return f'MCall({c2}, args={self.args}, args_is_float={self.args_is_float}, tail={self.tail}, dsts={self.dsts}, dsts_is_float={self.dsts_is_float})'


@dataclass
class MCallIntrinsic(I):
    intrinsic: LiteralString
    args: list[PhyReg | Id]
    args_is_float: list[bool]
    tail: bool
    dsts: list[Id | PhyReg] = field(default_factory=list)
    dsts_is_float: list[bool] = field(default_factory=list)

    def __post_init__(self):
        assert len(self.args) == len(self.args_is_float)
        assert len(self.dsts) == len(self.dsts_is_float)



@dataclass
class MRet(I):
    def __str__(self):
        return 'ret'


@dataclass
class Nop(I): ...

@dataclass
class MBinaryInt(MBinary): is_float = False, False, False

@dataclass
class MBinaryFloat(MBinary): is_float = True, True, True

@dataclass
class MAdd(MBinaryInt): opcode: ClassVar[str] = 'add'


@dataclass
class MSub(MBinaryInt): opcode: ClassVar[str] = 'sub'


@dataclass
class MMul(MBinaryInt): opcode: ClassVar[str] = 'mul'


@dataclass
class MDiv(MBinaryInt): opcode: ClassVar[str] = 'div'


@dataclass
class MXor(MBinaryInt): opcode: ClassVar[str] = 'xor'



@dataclass
class MFAdd(MBinaryFloat): opcode: ClassVar[str] = 'fadd.s'


@dataclass
class MFSub(MBinaryFloat): opcode: ClassVar[str] = 'fsub.s'


@dataclass
class MFMul(MBinaryFloat): opcode: ClassVar[str] = 'fmul.s'


@dataclass
class MFDiv(MBinaryFloat): opcode: ClassVar[str] = 'fdiv.s'


@dataclass
class MCmp(MBinary): is_float = False, False, False


@dataclass
class MEq(MCmp): ...


@dataclass
class MNeq(MCmp): ...


@dataclass
class MLt(MCmp): opcode: ClassVar[str] = 'slt'


@dataclass
class MLe(MCmp): ...


@dataclass
class MFCmp(MBinary): is_float = True, True, False


@dataclass
class MFEq(MFCmp): opcode: ClassVar[str] = 'feq.s'


@dataclass
class MFNeq(MFCmp): ...


@dataclass
class MFLt(MFCmp): opcode: ClassVar[str] = 'flt.s'


@dataclass
class MFLe(MFCmp): opcode: ClassVar[str] = 'fle.s'


@dataclass
class MBinaryImm(I):
    opcode: ClassVar[str]
    src: Id | PhyReg
    imm: int
    dst: Id | PhyReg = field(default_factory=Id)

    def __str__(self):
        return f'{self.opcode} {self.dst!r}, {self.src!r}, {self.imm}'


@dataclass
class MSlli(MBinaryImm):
    opcode: ClassVar[str] = 'slli'

    def __post_init__(self):
        assert 0 <= self.imm < 32


@dataclass
class MSrai(MBinaryImm):
    opcode: ClassVar[str] = 'srai'

    def __post_init__(self):
        assert 0 <= self.imm < 32


@dataclass
class MAddi(MBinaryImm):
    opcode: ClassVar[str] = 'addi'


    def __post_init__(self):
        assert -2048 <= self.imm < 2048

@dataclass 
class MXori(MBinaryImm):
    opcode: ClassVar[str] = 'xori'

    def __post_init__(self):
        assert -2048 <= self.imm < 2048


@dataclass
class MArg:
    src: list[Id | PhyReg] = field(default_factory=list)
    is_float: list[bool] = field(default_factory=list)

    def __post_init__(self):
        assert len(self.src) == len(self.is_float)


class MFunction:
    global_var_addr: Mapping[Id, tuple[Id, int]] = {}
    global_var_gp_offset: Mapping[Id, int] = {}
    float_table: Mapping[float, Id] = {}

    def __init__(self, funct: Id, typ: TyFun):
        self.funct = funct
        # self.is_rec = 0
        self.typ = typ
        self.n_words_pass_by_stack = 0
        self.n_words_return_by_stack = 0
        self.ra = Id(f'{funct}.ra')
        # self.funct_usage = 0
        self.formal_fv: dict[Id, MArg] = {}
        self.formal_args: dict[Id, MArg] = {}
        # self.local_vars: Mapping[Id, Sequence[Id]] = {}
        self.is_float: dict[Id, bool] = {}
        # self.usage: dict[Id, int] = {}
        # self.live_interval: dict[Id, list[int]] = {}
        # self.reg_alloc: dict[Id, PhyReg] = {}
        # self.stack_slot: dict[Id, StackSlot] = {}
        
        self.preparation: list[I] = []
        self.body: list[I] = []

    def __repr__(self):
        return f'MFunction({self.funct!r}, {self.funct}, {self.typ!r})'


class MFunctionMain(MFunction):
    def __repr__(self):
        return f'MMain({self.funct!r}, {self.funct}, {self.typ!r})'

@lru_cache
def abi_size(t: Ty, /):
    match t:
        case TyUnit():
            return 0
        case TyInt() | TyBool() | TyFloat() | TyArray():
            return 4
        case TyTuple():
            return sum(map(abi_size, t.elems))
        case TyFun():
            return 8
        case _:
            raise NotImplementedError(t)


from collections.abc import Iterable


def iter_is_float(t: Ty, /) -> Iterable[bool]:
    match t:
        case TyUnit():
            return
        case TyFloat():
            yield True
        case TyTuple():
            for elem in t.elems:
                yield from iter_is_float(elem)
        case TyArray() | TyInt() | TyBool():
            yield False
        case TyFun():
            yield False
            yield False
        case _:
            raise NotImplementedError(t)


def iter_ty(t: Ty, /) -> Iterable[Ty]:
    match t:
        case TyInt() | TyBool() | TyFloat() | TyArray():
            yield t
        case TyTuple():
            for elem in t.elems:
                yield from iter_ty(elem)
        case TyFun():
            yield t
            yield TyInt()
        case TyUnit():
            return
        case _:
            raise NotImplementedError(t)

def break_out(ty: Ty, v: Id | None = None, /, descr: str = '') -> tuple[Id, ...] | tuple[()]:
    assert abi_size(ty) & 3 == 0
    match abi_size(ty) // 4:
        case 0:
            return ()
        case 1:
            return v or Id(descr),
        case k:
            if v is None:
                return tuple(Id(f'{descr}:sub_{i}') for i in range(k))
            return tuple(Id(f'{v}:sub_{i}') for i in range(k))


class Select:
    def __init__(self, preludes: dict[Id, Ty], array_makes: dict[Id, Ty], globals: dict[Id, Ty]):
        self.env = ChainMap(dict(globals), preludes | array_makes)
        self.functions: dict[Id, MFunction] = {}
        
        self.val = ChainMap[Id, tuple[Id, ...] | tuple[()]]()
        self.float_table: dict[float, Id] = {}
        self.array_make_cache: dict[tuple[str, int], MFunction] = {}
        
        global_val: dict[Id, tuple[Id, ...]] = {}
        global_val_addr: dict[Id, tuple[Id, int]] = {}
        static_val_gp_offset: dict[Id, int] = {}
        env1: dict[Id, Ty] = {}
        offset = 0
        for k, v in self.env.items():
            if isinstance(v, TyFun):
                global_val[k] = k,
                # global_val_addr[k] = k, 0
            else:
                ids = break_out(v, k)
                global_val[k] = ids
                static_val_gp_offset[k] = offset
                for i, (x, t) in enumerate(zip(ids, iter_ty(v), strict=True)):
                    global_val[x] = x,
                    global_val_addr[x] = k, i
                    static_val_gp_offset[x] = offset
                    env1[x] = t
                    offset += 4

        self.env.update(env1)
        
        for k, v in array_makes.items():
            self.functions[k] = am = self.select_array_make(k, v)
            self.functions[am.funct] = am
            global_val[k] = am.funct,
            global_val[am.funct] = am.funct,
            # global_val_addr[k] = am.funct, 0
        
        self.val.update(global_val)
        self.global_val_addr: Mapping[Id, tuple[Id, int]] = global_val_addr
        self.static_val_gp_offset = static_val_gp_offset
        self.gp_offset_top = offset
    
    def update_env(self, env: dict[Id, Ty]):
        assert self.env.keys().isdisjoint(env.keys())
        break_outs = {k: break_out(v, k) for k, v in env.items()}
        self.env.update(env)
        for k, xs in break_outs.items():
            self.val[k] = tuple(xs)
            if len(xs) > 1:
                for x, t in zip(xs, iter_ty(env[k]), strict=True):
                    self.val[x] = x,
                    self.env[x] = t

    @contextlib.contextmanager
    def new_child_env(self, env: dict[Id, Ty]):
        self.env = self.env.new_child()
        self.val = self.val.new_child()
        self.update_env(env)
        try:
            yield
        finally:
            self.env = self.env.parents
            self.val = self.val.parents
    
    @overload
    def find_val(self, x: Id, silent: Literal[False]=False, /) -> tuple[Id, ...] | tuple[()]: ...

    @overload
    def find_val(self, x: Id, silent: Literal[True], /) -> tuple[Id, ...] | tuple[()] | None: ...
    
    def find_val(self, x: Id, silent: bool = False, /) -> tuple[Id, ...] | tuple[()] | None:
        match self.val.get(x):
            case [y] as v:
                if y == x:
                    return v
                self.val[x] = z = self.find_val(y)
                return z
            case tuple() as ys:
                z = sum((self.find_val(y) for y in ys), ())
                if z != ys:
                    self.val[x] = z
                return z
            case None:
                if silent:
                    return None
                raise KeyError(x)

    def lookup(self, x: Id, /):
        return self.env[x], self.find_val(x)


    def select_array_make(self, name: Id, ty: Ty, /):
        match ty:
            case TyFun([TyInt(), elem], TyArray(elem1)) if elem == elem1:
                is_floats = tuple(iter_is_float(elem))
                n_args_on_reg = min(7, is_floats.count(False))
                n_args_on_float_reg = min(8, is_floats.count(True))
                n_args_on_stack = len(is_floats) - n_args_on_reg - n_args_on_float_reg
                k1 = ''.join(map(lambda x: str(int(x)), is_floats[:n_args_on_reg + n_args_on_float_reg]))
                try:
                    return self.array_make_cache[k1, n_args_on_stack]
                except KeyError:
                    ...
                tp = PhyReg('tp')
                fp = PhyReg('fp')
                t = tuple(PhyReg(f't{i}') for i in range(7))
                ft = tuple(PhyReg(f'ft{i}') for i in range(12))
                assert 1 + n_args_on_stack <= len(t) + len(ft), 'too many arguments on stack to fit in to t1-t6 and ft0-ft11'
                a = tuple(PhyReg(f'a{i}') for i in range(8))
                fa = tuple(PhyReg(f'fa{i}') for i in range(8))
                mf = MFunction(Id(f"create_array_{k1}_{n_args_on_stack}"), ty)
                mf.n_words_pass_by_stack = n_args_on_stack

                # mf.body.append(MCopy(False, PhyReg('ra'), mf.ra))
                mf.body.append(MCopy(False, tp, t[0]))

                args_on_stack_iter = iter(reversed(range(n_args_on_stack)))
                for src, dst in zip(args_on_stack_iter, t[1:]):
                    mf.body.append(MLoad(False, fp, -4 * src - 4, dst))
                for src, dst in zip(args_on_stack_iter, ft):
                    mf.body.append(MLoad(True, fp, -4 * src - 4, dst))

                loop_label = MLabel(Id('loop'))
                loop_body = MSeq([])
                loop = MIf(a[0], loop_body, Nop(), [], [])
                i, j, k = 0, 0, 0
                while i + j + k < len(is_floats):
                    if is_floats[i + j + k] and j < n_args_on_float_reg:
                        loop_body.instrs.append(MStore(True, fa[j], tp, (i + j + k) * 4))
                        j += 1
                    elif i < n_args_on_reg:
                        loop_body.instrs.append(MStore(False, a[i + 1], tp, (i + j + k) * 4))
                        i += 1
                    elif k + 1 < len(t):
                        loop_body.instrs.append(MStore(False, t[k + 1], tp, (i + j + k) * 4))
                        k += 1
                    else:
                        loop_body.instrs.append(MStore(True, ft[k + 1 - len(t)], tp, (i + j + k) * 4))
                        k += 1

                loop_body.instrs.append(MAddi(tp, (i + j + k) * 4, tp))
                loop_body.instrs.append(MAddi(a[0], -1, a[0]))
                loop_body.instrs.append(MJump(loop_label))
                mf.body.append(loop_label)
                mf.body.append(loop)
                mf.body.append(MCopy(False, t[0], a[0]))
                # mf.body.append(MCopy(False, PhyReg('ra'), mf.ra))
                mf.body.append(MRet())
                self.array_make_cache[k1, n_args_on_stack] = mf
                return mf
            case _:
                raise ValueError(ty)

    def select_program(self, prog: Program):
        assert self.env.keys().isdisjoint(f.funct for f in prog.fns)
        for f in prog.fns:
            self.env[f.funct] = f.typ
            self.val[f.funct] = f.funct,
            self.functions[f.funct] = MFunction(f.funct, f.typ)

        MFunction.global_var_addr = self.global_val_addr
        MFunction.float_table = MLoadFloatImm.float_table = self.float_table
        MFunction.global_var_gp_offset = self.static_val_gp_offset
        n = len(self.env.maps[0])
        for f in prog.fns:
            assert len(self.env.maps) == 2
            assert len(self.env.maps[0]) == n
            self.visit_Function(f)

        main = MFunctionMain(Id('main'), TyFun(TyUnit(), TyUnit()))
        main.preparation.append(MCopy(False, PhyReg('ra'), main.ra))
        for e in prog.exp_or_cls_or_letbindings:
            assert len(self.env.maps) == 2
            match e:
                case Exp():
                    main.body.extend(self.visit(e, (), main.ra))
                case Cls():
                    raise NotImplementedError(e)
                    self.visit_Cls(e)
                case LetBinding():
                    main.body.extend(self.visit_LetBinding(e, main.ra))
                    assert e.lhs in self.env
        main.body.append(MCopy(False, main.ra, PhyReg('ra')))
        main.body.append(MRet())
        return {f.funct: self.functions[f.funct] for f in prog.fns}, main

    def visit(self, e: Exp[Ty], /, target_ids: Sequence[Id], ra: Id, tail: bool = False) -> list[I]:
        def load_global(is_float: bool, src: Id, dst: Id | PhyReg, /):
            # start, idx = self.global_val_addr[src]
            # hi = Id(f'{src}.hi')
            # seq: list[I] = [MLuiHi(start, hi)]
            # if idx:
            #     added = Id(f'{src}.added')
            #     addi = MAddi(hi, 4 * idx, added)
            #     seq.append(addi)
            #     hi = added      

            # seq.append(MLoadLo(is_float, hi, start, dst))
            # return seq
            return [MLoad(is_float, PhyReg.gp, self.static_val_gp_offset[src], dst)]

        def load_float(imm: float, dst: Id | PhyReg, /) -> list[I]:
            match imm:
                case 0.0:
                    return [MLoadFZero(target_id)]
                case 0.5:
                    tmp = Id(f'{target_id}.tmp')
                    return [MLui(0x3f000, tmp), MFMvWX(tmp, target_id)]
                case 1.0:
                    tmp = Id(f'{target_id}.tmp')
                    return [MLui(0x3f800, tmp), MFMvWX(tmp, target_id)]
                case -1.0:
                    tmp = Id(f'{target_id}.tmp')
                    return [MLui(0xbf800, tmp), MFMvWX(tmp, target_id)]
                case _:
                    from struct import pack, unpack
                    imm = unpack('f', pack('f', imm))[0]
                    try:
                        _ = self.float_table[imm]
                    except KeyError:
                        self.float_table[imm] = label = Id(f'.LC{len(self.float_table)}')
                        self.static_val_gp_offset[label] = self.gp_offset_top
                        self.gp_offset_top += 4
                    return [MLoadFloatImm(imm, dst)]

        def store_global(is_float: bool, src: Id | PhyReg, dst: Id, /):
            start, idx = self.global_val_addr[dst]
            hi_dst = Id(f'{src}.hi')
            seq: list[I] = [MLuiHi(start, hi_dst)]
            if idx:
                addi = MAddi(src, 4 * idx)
                seq.append(addi)
                hi_dst = addi.dst

            seq.append(MStoreLo(is_float, src, hi_dst, start))
            return seq
        
        # def partition(xs: Iterable[Id], is_floats: Iterable[bool], /):
        #     ints: list[Id] = []
        #     floats: list[Id] = []
        #     for x, is_float in zip(xs, is_floats, strict=True):
        #         if is_float:
        #             floats.append(x)
        #         else:
        #             ints.append(x)
        #     return ints, floats

        # def update_ra(callee: Id | str, /):
        #     ra0, = self.val[ra]
        #     ra1 = Id(f'{callee}.ret.ra1')
        #     self.val[ra1] = ra1,
        #     return ra1, ra0


        match e, target_ids:
            case LitU(), []:
                return []
            case LitI() | LitB(), [target_id]:
                self.val[target_id] = target_id,
                return [MLoadImm(e.lit, target_id)]
            case LitF(lit), [target_id]:
                self.val[target_id] = target_id,
                return load_float(lit, target_id)
            case Var(), _:
                ty, vals = self.lookup(e.name)
                if isinstance(ty, TyFun):
                    raise NotImplementedError(ty)
                assert set(target_ids).isdisjoint(vals)
                for src, dst in zip(vals, target_ids, strict=True):
                    assert self.val[src] == (src,)
                    self.val[dst] = src,
                return []
            case Get(), _:
                match self.lookup(e.array), self.lookup(e.index), target_ids:
                    case [TyArray(elem), [array_v]], [_, [index_v]], _:
                        seq: list[I] = []
                        if array_v in MFunction.global_var_addr:
                            loaded = Id(f'{array_v}.loaded')
                            seq.extend(load_global(False, array_v, loaded))
                            # self.val[array_v] = loaded,
                        else:
                            loaded = array_v
                            # loaded = Id(f'{array_v}.copy')
                            # seq.append(MCopy(False, array_v, loaded))

                        del array_v

                        # index_v2 = Id(f'{index_v}.copy')
                        # seq.append(MCopy(False, index_v, index_v2))
                        # mul4 = MSlli(index_v2, 2)
                        # mul4 = MSlli(index_v, 2)
                        load_sizeof = MLoadImm(abi_size(elem), Id(f'{elem}.sizeof'))
                        mul = MMul(index_v, load_sizeof.dst, Id('index.mul.sizeof'))
                        add = MAdd(loaded, mul.dst)
                        seq.append(load_sizeof)
                        seq.append(mul)
                        seq.append(add)
                        match abi_size(elem) // 4, target_ids, tuple(iter_is_float(elem)):
                            case 0, [], []:
                                seq.append(MLoad(False, add.dst, 0))
                            case 1, [target_id], [is_float]:
                                self.val[target_id] = target_id,
                                seq.append(MLoad(is_float, add.dst, 0, target_id))
                            case _, _, is_floats:
                                for is_float, i, target_id in zip(is_floats, range(0, abi_size(elem), 4), target_ids, strict=True):
                                    self.val[target_id] = target_id,
                                    seq.append(MLoad(is_float, add.dst, i, target_id))
                        return seq
                    case [array_t, array_v], [index_t, index_v], _:
                        raise ValueError(array_t, array_v, index_t, index_v, target_ids)                        
                
            case Unary(), [target_id]:
                _, y_v = self.lookup(e.y)
                match y_v:
                    case [Id() as y]:
                        self.val[target_id] = target_id,
                        match e.op:
                            case UnaryOpKind.I_NEG:
                                return [MNeg(y, target_id)]
                            case UnaryOpKind.F_NEG:
                                return [MFNeg(y, target_id)]
                    case _:
                        raise ValueError(y_v)
            case AppDir(), _:
                match self.env[e.callee], self.val[e.callee]:
                    case _, [callee_v] if callee_v.is_intrinsic():
                        match sum((self.lookup(arg)[1] for arg in e.args), ()), target_ids:
                            case [arg1, arg2], [target_id] if callee_v.is_intrinsic('xor'):
                                self.val[target_id] = target_id,
                                return [MXor(arg1, arg2, target_id)]
                            case [arg], [] if callee_v.is_intrinsic('print_int'):
                                return [MCallIntrinsic('print_int', [arg], [False], tail, [], [])]
                            case [arg], [] if callee_v.is_intrinsic('print_char'):
                                return [MOut(arg)]
                            case [arg], [] if callee_v.is_intrinsic('assert_nvector'):
                                tmp = Id('minus1')
                                return [MLoadImm(-1, tmp), MCout(False, arg), MIf(MEq(tmp, arg), MSimuHalt(), Nop(), [], [])]
                            case [arg], [target_id]:
                                self.val[target_id] = target_id,
                                if callee_v.is_intrinsic('not'):
                                    return [MSeqz(arg, target_id)]
                                elif callee_v.is_intrinsic('fsqr'):
                                    return [MFMul(arg, arg, target_id)]
                                elif callee_v.is_intrinsic('fneg'):
                                    return [MFNeg(arg, target_id)]
                                elif callee_v.is_intrinsic('sqrt'):
                                    return [MFSqrt(arg, target_id)]
                                elif callee_v.is_intrinsic('fispos'):
                                    z = MLoadFZero()
                                    return [z, MFLt(z.dst, arg, target_id)]
                                elif callee_v.is_intrinsic('fisneg'):
                                    z = MLoadFZero()
                                    return [z, MFLt(arg, z.dst, target_id)]
                                elif callee_v.is_intrinsic('fiszero'):
                                    z = MLoadFZero()
                                    return [z, MFEq(arg, z.dst, target_id)]
                                elif callee_v.is_intrinsic('fabs'):
                                    return [MFAbs(arg, target_id)]
                                elif callee_v.is_intrinsic('fhalf'):
                                    half = Id('half')
                                    return load_float(0.5, half) + [MFMul(arg, half, target_id)]
                                elif callee_v.is_intrinsic('sin') or callee_v.is_intrinsic(
                                        'cos') or callee_v.is_intrinsic('floor') or callee_v.is_intrinsic('atan'):
                                    if callee_v.is_intrinsic('sin'):
                                        intrinsic = 'mincaml_sin'
                                    elif callee_v.is_intrinsic('cos'):
                                        intrinsic = 'mincaml_cos'
                                    elif callee_v.is_intrinsic('floor'):
                                        intrinsic = 'mincaml_floor'
                                    else:  # callee_v.is_intrinsic('atan')
                                        intrinsic = 'mincaml_atan'
                                    seq = [MCallIntrinsic(intrinsic,  [arg], [True], tail, [target_id], [True])]
                                    # if not tail:
                                    #     seq.append(MCopy(True, PhyReg('fa0'), target_id))
                                    return seq
                                elif callee_v.is_intrinsic('int_of_float'):
                                    return [MFCvtWS(arg, target_id)]
                                elif callee_v.is_intrinsic('float_of_int'):
                                    return [MFCvtSW(arg, target_id)]

                            case [], [target_id]:
                                self.val[target_id] = target_id,
                                if callee_v.is_intrinsic('read_int'):
                                    return [MCin(False, target_id)]
                                    # return [MCall(Label(callee_v), tail, [False], [target_id])]
                                elif callee_v.is_intrinsic('read_float'):
                                    return [MCin(True, target_id)]
                                    # return [MCall(Label(callee_v), tail, [True], [target_id])]
                            case [], []:
                                if callee_v.is_intrinsic('print_newline'):
                                    return [MOut(Id('newline'))]
                                else:
                                    raise ValueError(callee_v)
                            case _:
                                ...
                        raise ValueError(str(callee_v), e.args, target_ids)
                    case TyFun(_, ret), [callee_v]:
                        seq: list[I] = []
                        args: list[Id | PhyReg] = []
                        args_is_float: list[bool] = []
                        for arg in e.args:
                            arg_ty, arg_v = self.lookup(arg)
                            for is_float, src in zip(iter_is_float(arg_ty), arg_v, strict=True):
                                args.append(src)
                                args_is_float.append(is_float)

                        # TODO: tail call
                        seq.append(MCall(self.functions[callee_v], args, args_is_float, tail, list(target_ids), list(iter_is_float(ret))))
                        for target_id in target_ids:
                            self.val[target_id] = target_id,

                        return seq
                    case _, callee_v:
                        raise ValueError(callee_v)

            case AppCls(), _:
                raise NotImplementedError(e)
            case Binary(), [target_id]:
                self.val[target_id] = target_id,
                ty, y1_v = self.lookup(e.y1)
                _, y2_v = self.lookup(e.y2)

                match y1_v, y2_v, list(iter_is_float(ty)):
                    case [y1], [y2], [is_float]:
                        # y1_ = Id(f'{y1}.copy')
                        # y2_ = Id(f'{y2}.copy')
                        # target_id_ = Id(f'{target_id}.copy')
                        # y1_copy = MCopy(is_float, y1, y1_)
                        # y2_copy = MCopy(is_float, y2, y2_)
                        # target_copy = MCopy(is_float, target_id_, target_id)
                        # seq = [y1_copy, y2_copy, target_copy]
                        y1_, y2_, target_id_ = y1, y2, target_id
                        seq: list[I] = []
                        match e.op:
                            case BinaryOpKind.I_ADD:
                                seq.insert(-1, MAdd(y1_, y2_, target_id_))
                            case BinaryOpKind.I_SUB:
                                seq.insert(-1, MSub(y1_, y2_, target_id_))
                            case BinaryOpKind.I_MUL:
                                seq.insert(-1, MMul(y1_, y2_, target_id_))
                            case BinaryOpKind.I_DIV:
                                seq.insert(-1, MDiv(y1_, y2_, target_id_))
                            case BinaryOpKind.F_ADD:
                                seq.insert(-1, MFAdd(y1_, y2_, target_id_))
                            case BinaryOpKind.F_SUB:
                                seq.insert(-1, MFSub(y1_, y2_, target_id_))
                            case BinaryOpKind.F_MUL:
                                seq.insert(-1, MFMul(y1_, y2_, target_id_))
                            case BinaryOpKind.F_DIV:
                                seq.insert(-1, MFDiv(y1_, y2_, target_id_))
                            case BinaryOpKind.I_EQ | BinaryOpKind.B_EQ:
                                xor = MXor(y1_, y2_)
                                seq[-1:-1] = [xor, MSeqz(xor.dst, target_id_)]
                            case BinaryOpKind.I_NEQ | BinaryOpKind.B_NEQ:
                                seq.insert(-1, MXor(y1_, y2_, target_id_))
                            case BinaryOpKind.I_LT:
                                seq.insert(-1, MLt(y1_, y2_, target_id_))
                            case BinaryOpKind.I_LE:  # y1 <= y2 <=> not (y2 < y1)
                                lt = MLt(y2_, y1_)
                                seq[-1:-1] = [lt, MSeqz(lt.dst, target_id_)]
                            case BinaryOpKind.I_GT:
                                seq.insert(-1, MLt(y2_, y1_, target_id_))
                            case BinaryOpKind.I_GE:  # y1 >= y2 <=> not (y1 < y2)
                                lt = MLt(y1_, y2_)
                                seq[-1:-1] = [lt, MSeqz(lt.dst, target_id_)]
                            case BinaryOpKind.F_EQ:
                                # target_copy.is_float = False
                                seq.insert(-1, MFEq(y1_, y2_, target_id_))
                            case BinaryOpKind.F_NEQ:
                                # target_copy.is_float = False
                                seq.insert(-1, MFNeq(y1_, y2_, target_id_))
                            case BinaryOpKind.F_LT:
                                # target_copy.is_float = False
                                seq.insert(-1, MFLt(y1_, y2_, target_id_))
                            case BinaryOpKind.F_LE:
                                # target_copy.is_float = False
                                seq.insert(-1, MFLe(y1_, y2_, target_id_))
                            case BinaryOpKind.F_GT:
                                # target_copy.is_float = False
                                seq.insert(-1, MFLt(y2_, y1_, target_id_))
                            case BinaryOpKind.F_GE:
                                # target_copy.is_float = False
                                seq.insert(-1, MFLe(y2_, y1_, target_id_))
                    case _:
                        raise ValueError(y1_v, y2_v)
                return seq
            case Seq(), _:
                seq: list[I] = []
                for i in range(len(e.es) - 1):
                    seq.extend(self.visit(e.es[i], (), ra))
                seq.extend(self.visit(e.es[-1], target_ids, ra, tail))
                return seq
            case Tuple(), _:
                tup = [self.lookup(x) for x in e.ys]
                tup_v = sum([list(v) for _, v in tup], list[Id]())
                for src, dst in zip(tup_v, target_ids, strict=True):
                    self.val[dst] = src,
                return []
            case Put(), _:
                seq: list[I] = []
                match self.lookup(e.array), self.lookup(e.index), self.lookup(e.value):
                    case [TyArray(elem), [array_v]], [_, [index_v]], [_, value_v]:
                        if array_v in MFunction.global_var_addr:
                            loaded = Id(f'{array_v}.loaded')
                            seq.extend(load_global(False, array_v, loaded))
                            # self.val[array_v] = loaded, 
                        else:
                            # loaded = Id(f'{array_v}.copy')
                            # seq.append(MCopy(False, array_v, loaded))
                            loaded = array_v

                        # index_v2 = Id(f'{index_v}.copy')
                        # seq.append(MCopy(False, index_v, index_v2))
                        # mul4 = MSlli(index_v2, 2)
                        # mul4 = MSlli(index_v, 2)
                        load_sizeof = MLoadImm(abi_size(elem), Id(f'{elem}.sizeof'))
                        mul = MMul(index_v, load_sizeof.dst, Id('index.mul.sizeof'))
                        where = MAdd(loaded, mul.dst)
                        seq.append(load_sizeof)
                        seq.append(mul)
                        seq.append(where)
                        for is_float, src, offset in zip(iter_is_float(elem), value_v, range(0, abi_size(elem), 4), strict=True):
                            seq.append(MStore(is_float, src, where.dst, offset))
                        return seq
                    case [_, array_v], [_, index_v], [_, value_v]:
                        raise ValueError(array_v, index_v, value_v)
            case If(), _:
                match self.lookup(e.cond):
                    case [TyBool(), [cond_v]]:
                        self.val = self.val.new_child()
                        instrs_true = self.visit(e.br_true, target_ids, ra, tail)
                        target_ids_trues = tuple(self.find_val(x, True) for x in target_ids)
                        self.val = self.val.parents.new_child()

                        instrs_false = self.visit(e.br_false, target_ids, ra, tail)
                        target_ids_falses = tuple(self.find_val(x, True) for x in target_ids)
                        self.val = self.val.parents

                        for is_float, target_id, target_ids_true, target_ids_false in \
                                zip(iter_is_float(e.typ), target_ids, target_ids_trues, target_ids_falses, strict=True):
                            match target_ids_true, target_ids_false:
                                case None, None:
                                    assert target_id not in self.val
                                case [target_id_true], [target_id_false] if target_id_true == target_id_false:
                                    assert self.val.setdefault(target_id, (target_id_true,)) == (target_id_true,)
                                case [target_id_true], [target_id_false]:
                                    if target_id_true != target_id:
                                        instrs_true.append(MCopy(is_float, target_id_true, target_id))
                                    if target_id_false != target_id:
                                        instrs_false.append(MCopy(is_float, target_id_false, target_id))
                                    self.val[target_id] = target_id,
                                case _, _:
                                    raise ValueError(target_ids_true, target_ids_false)
                        match instrs_true:
                            case []:
                                br_true = Nop()
                            case [instr]:
                                br_true = instr
                            case instrs:
                                br_true = MSeq(instrs)
                        match instrs_false:
                            case []:
                                br_false = Nop()
                            case [instr]:
                                br_false = instr
                            case instrs:
                                br_false = MSeq(instrs)

                        return [MIf(cond_v, br_true, br_false, list(iter_is_float(e.typ)), list(target_ids))]
                    case [_, cond_v]:
                        raise ValueError(cond_v)
            case Let(), _:
                let_target_ids = break_out(e.binding.rhs.typ, e.binding.lhs)
                seq = self.visit(e.binding.rhs, let_target_ids, ra)
                assert e.binding.lhs not in self.env
                self.env[e.binding.lhs] = e.binding.rhs.typ
                self.val[e.binding.lhs] = sum(map(self.find_val, let_target_ids), ())
                return seq + self.visit(e.expr, target_ids, ra, tail)
            case LetTuple(), _:
                assert self.env.keys().isdisjoint(e.xs)
                _, y_v = self.lookup(e.y)
                self.env.update(dict(zip(e.xs, e.ts)))
                i = 0
                for x, t in zip(e.xs, e.ts):
                    self.val[x] = y_v[i:i + abi_size(t) // 4]
                    i += abi_size(t) // 4
                return self.visit(e.e, target_ids, ra, tail)

            case MakeCls(), _:
                self.visit_Cls(e.closure)
                return self.visit(e.body, target_ids, ra,  tail)
            case _:
                raise NotImplementedError(e, target_ids)

    def visit_LetBinding(self, binding: LetBinding, ra: Id):
        
        with self.new_child_env({}):
            seq = self.visit(binding.rhs, self.val[binding.lhs], ra, tail=False)

            self.find_val(binding.lhs)
            parents = self.val.parents
            copyfrom: dict[Id, Id] = {}
            for k, v in self.val.maps[0].items():
                try:
                    v0 = parents[k]
                    assert len(v) == len(v0)
                    for vv, vv0 in zip(v, v0):
                        if vv != vv0:
                            if vv0 not in copyfrom:
                                copyfrom[vv0] = vv
                            else:
                                assert copyfrom[vv0] == vv
                except KeyError:
                    pass
            for d, s in copyfrom.items():
                seq.append(MCopy(next(iter(iter_is_float(self.env[d]))), s, d))
        return seq
        # target_ids = break_out(binding.rhs.typ, binding.lhs)
        # seq = self.visit(binding.rhs, target_ids, ra)
        # assert self.env[binding.lhs] == binding.rhs.typ
        # for is_float, src, dst in zip(iter_is_float(binding.rhs.typ), sum([self.val[v] for v in target_ids], ()), self.val[binding.lhs], strict=True):
        #     if src != dst:
        #         seq.append(MCopy(is_float, src, dst))
        # return seq

    def visit_Cls(self, cls: Cls):
        assert cls.entry.funct in self.env
        for actual_fv, (_, formal_fv_ty) in zip(cls.actual_fv, cls.entry.formal_fv, strict=True):
            assert formal_fv_ty == self.lookup(actual_fv)

    def visit_Function(self, f: Function):
        mf = self.functions[f.funct]
        with self.new_child_env(dict(zip(f.formal_args, f.typ.args, strict=True))):
            self.update_env(dict(f.formal_fv))

            mf.formal_args = {k: MArg(list(self.val[k]), list(iter_is_float(ty))) for k, ty in
                              zip(f.formal_args, f.typ.args)}
            mf.formal_fv = {k: MArg(list(self.val[k]), list(iter_is_float(ty))) for k, ty in f.formal_fv}

            # s_saved = {i: Id(f's{i}.save') for i in range(12)}
            mf.preparation.append(MCopy(False, PhyReg('ra'), mf.ra))
            # for i, s in s_saved.items():
            #     mf.preparation.append(MCopy(False, PhyReg(f's{i}'), s))
            # fs_saved = {i: Id(f'fs{i}.save') for i in range(12)}
            # for i, fs in fs_saved.items():
            #     mf.preparation.append(MCopy(True, PhyReg(f'fs{i}'), fs))

            instrs: list[I] = []
            is_floats = tuple(b for t in f.typ.args for b in iter_is_float(t))
            mf.n_words_pass_by_stack = max(0, is_floats.count(True) - 8) + max(0, is_floats.count(False) - 8)
            i, j, k = 0, 0, -4 * mf.n_words_pass_by_stack
            for arg in mf.formal_args.values():
                for is_float, src in zip(arg.is_float, arg.src, strict=True):
                    if is_float and j < 8:
                        instrs.append(MCopy(is_float, PhyReg(f'fa{j}'), dst=src))
                        j += 1
                    elif not is_float and i < 8:
                        instrs.append(MCopy(is_float, PhyReg(f'a{i}'), dst=src))
                        i += 1
                    else:
                        # tmp = PhyReg('ft11')
                        instrs.append(MLoad(is_float, PhyReg('fp'), k, dst=src))
                        # if is_float:
                        #     instrs.append(MCopy(is_float, tmp, src))
                        # else:
                        #     instrs.append(MFMvXW(tmp, src))
                        k += 4

            ret = break_out(f.typ.ret, descr='ret')
            is_floats = tuple(iter_is_float(f.typ.ret))
            mf.n_words_return_by_stack = max(0, is_floats.count(True) - 2) + max(0, is_floats.count(False) - 2)

            def epilogue(ret: Sequence[Id] | None = None):
                ret = ret or break_out(f.typ.ret, descr='ret')
                seq: list[I] = []
                i, j, k = 0, 0, -4 * mf.n_words_return_by_stack
                for is_float, src in zip(iter_is_float(f.typ.ret), ret, strict=True):
                    match self.val.get(src, (src,)):
                        case [src]:
                            if is_float and j < 2:
                                seq.append(MCopy(is_float, src, PhyReg(f'fa{j}')))
                                j += 1
                            elif not is_float and i < 2:
                                seq.append(MCopy(is_float, src, PhyReg(f'a{i}')))
                                i += 1
                            else:
                                seq.append(MStore(is_float, src, PhyReg('fp'), k))
                                k += 4
                        case _:
                            raise ValueError(src)

                # for i, s in reversed(s_saved.items()):
                #     seq.append(MCopy(False, s, PhyReg(f's{i}')))
                # for i, s in reversed(fs_saved.items()):
                #     seq.append(MCopy(True, s, PhyReg(f'fs{i}')))
                seq.append(MCopy(False, mf.ra, PhyReg('ra')))
                seq.append(MRet())
                return seq

            instrs.extend(self.visit(f.body, ret, mf.ra, tail=True))
            instrs.extend(epilogue(ret))
            mf.body = instrs
            return mf


class LinearScan:
    As: Final = 8
    Ss: Final = 12
    Ts: Final = 6
    Fas: Final = 8
    Fss: Final = 12
    Fts: Final = 11
    caller_saved: Final = tuple([PhyReg(f'a{i}') for i in range(As)] + [PhyReg(f't{i}') for i in range(Ts)] + [PhyReg('ra')])
    callee_saved: Final = tuple(PhyReg(f's{i}') for i in range(Ss))
    caller_saved_f: Final = tuple([PhyReg(f'fa{i}') for i in range(Fas)] + [PhyReg(f'ft{i}') for i in range(Fts)])
    callee_saved_f: Final = tuple(PhyReg(f'fs{i}') for i in range(Fss))

    def __init__(self, builtins: set[Id], global_ids: Mapping[Id, tuple[Id, int]]):
        self.live_interval = ChainMap[Id, Interval]()
        self.favor = dict[Id, list[PhyReg]]()
        self.live_across_call = dict[Id, bool]()
        # self.call_pos: list[int] = []
        self.cur_pos = 0
        for b in builtins:
            self.live_interval[b] = Interval(0, 0)
        for v in global_ids:
            self.live_interval[v] = Interval(0, 0)

    def lookup(self, x: I | Id | PhyReg, increase: bool = True, /) -> TypeGuard[Id]:
        assert isinstance(x, Id)
        self.cur_pos += increase
        # self.call_pos.append(0)
        try:
            self.live_interval[x].end = self.cur_pos
        except KeyError:
            self.live_interval[x] = Interval(self.cur_pos, self.cur_pos)
        return True

    def add_favor(self, x: Id, reg: PhyReg):
        try:
            if reg not in self.favor[x]:
                self.favor[x].append(reg)
        except KeyError:
            self.favor[x] = [reg]

    def analyze_liveness(self, mf: MFunction):
        self.live_interval = self.live_interval.new_child()
        self.cur_pos = 0

        for instr in mf.preparation:
            self.visit(instr, mf.is_float)
        for instr in mf.body:
            self.visit(instr, mf.is_float)

        for instr in mf.preparation:
            self.visit_check(instr, mf.is_float)
        for instr in mf.body:
            self.visit_check(instr, mf.is_float)

        live_in = set[Id]()
        for instr in reversed(mf.body):
            self.live(instr, live_in)
        for instr in reversed(mf.preparation):
            self.live(instr, live_in)

        for x in self.live_interval.maps[0]:
            if self.live_across_call.get(x, False):
                if x in self.favor:
                    self.favor[x] = [r for r in self.favor[x] if r not in LinearScan.caller_saved_f and r not in LinearScan.caller_saved]
                    if mf.is_float[x]:
                        self.favor[x] += [r for r in LinearScan.callee_saved_f if r not in self.favor[x]]
                    else:
                        self.favor[x] += [r for r in LinearScan.callee_saved if r not in self.favor[x]]
                    if len(self.favor[x]) == 0:
                        del self.favor[x]
            else:
                self.live_across_call[x] = False

        res = self.live_interval.maps[0]
        return res, self.favor, self.live_across_call

    def visit(self, instr: I, is_float: dict[Id, bool], /): #, reads: dict[Id, int], writes: dict[Id, int],
        match instr:
            case MCopy(_is_float, src, dst):
                if isinstance(src, Id):
                    self.lookup(src)
                    is_float[src] = _is_float
                    if isinstance(dst, Id):
                        self.lookup(dst)
                        is_float[dst] = _is_float
                    else:
                        self.add_favor(src, dst)
                elif isinstance(dst, Id):
                    self.lookup(dst)
                    is_float[dst] = _is_float
                    self.add_favor(dst, src)

            case MLoadImm(_, Id() as dst) | MLui(_, Id() as dst) | MLuiHi(_, Id() as dst) | MCin(False, Id() as dst):
                self.lookup(dst)
                is_float[dst] = False
            case MLoadFZero(Id() as dst) | MCin(True, Id() as dst):
                self.lookup(dst)
                is_float[dst] = True
            case MLoadFloatImm(_idx, Id() as dst):
                # self.lookup(addr)
                # self.lookup(addr)
                self.lookup(dst)
                # is_float[addr] = False
                is_float[dst] = True
            case MLoad(_is_float, src=addr, offset=_, dst=val) | MStore(_is_float, val, addr, offset=_):
                if isinstance(addr, Id):
                    self.lookup(addr)
                    is_float[addr] = False
                    if isinstance(val, Id):
                        self.lookup(val)
                        is_float[val] = _is_float
                    elif not _is_float:
                        self.add_favor(addr, val)
                elif isinstance(val, Id):
                    self.lookup(val)
                    is_float[val] = _is_float
                    if not _is_float:
                        self.add_favor(val, addr)
            case MLoadLo(_is_float, src=addr, lo=_, dst=val) | MStoreLo(_is_float, val, addr, lo=_):
                if isinstance(addr, Id):
                    self.lookup(addr)
                    self.lookup(addr)
                    is_float[addr] = False
                    if isinstance(val, Id):
                        self.lookup(val)
                        is_float[val] = _is_float
                    elif not _is_float:
                        self.add_favor(addr, val)

            case MOut(Id() as src) | MCout(False, Id() as src):
                self.lookup(src)
                is_float[src] = False
            case MFCvtWS(Id() as s, Id() as w) | MFCvtSW(Id() as w, Id() as s) | MFMvWX(Id() as w, Id() as s) | MFMvXW(Id() as s, Id() as w):
                self.lookup(w)
                self.lookup(s)
                is_float[w] = False
                is_float[s] = True
            case MFMvWX(Id() as w, dst=PhyReg('ft11')) | MFMvXW(PhyReg('ft11'), Id() as w):
                self.lookup(w)
                is_float[w] = False
            case MUnary(Id() as src, Id() as dst):
                self.lookup(src)
                self.lookup(dst)
                is_float[dst] = is_float[src] = isinstance(instr, (MFNeg, MFSqrt, MFAbs))
            case MFCmp(Id() as src1, Id() as src2, Id() as dst):
                self.lookup(src1)
                self.lookup(src2)
                self.lookup(dst)
                is_float[src1] = is_float[src2] = True
                is_float[dst] = False
            case MBinary(Id() as src1, Id() as src2, Id() as dst):
                self.lookup(src1)
                self.lookup(src2)
                self.lookup(dst)
                is_float[dst] = is_float[src1] = is_float[src2] = isinstance(instr, (MFAdd, MFSub, MFMul, MFDiv))
            case MIf(Id() | MEq() as cond, br_true, br_false, _is_float, dst):
                if isinstance(cond, Id):
                    self.lookup(cond)
                    is_float[cond] = False
                else:
                    self.visit(cond, is_float)
                match br_true:
                    case list():
                        for i, b in enumerate(br_true):
                            assert isinstance(b, Id)
                            self.lookup(b)
                            is_float[b] = _is_float[i]
                    case I():
                        self.visit(br_true, is_float)

                match br_false:
                    case list():
                        for i, b in enumerate(br_false):
                            assert isinstance(b, Id)
                            self.lookup(b)
                            is_float[b] = _is_float[i]
                    case I():
                        self.visit(br_false, is_float)

                for i, d in enumerate(dst):
                    assert isinstance(d, Id)
                    self.lookup(d)
                    is_float[d] = _is_float[i]
            case MSeq(instrs):
                for instr in instrs:
                    self.visit(instr, is_float)
            case MCall(MFunction(), args, args_is_float, tail, dsts, dsts_is_float) | MCallIntrinsic(_, args, args_is_float, tail, dsts, dsts_is_float):
                assert is_id_list(args) and is_id_list(dsts)
                self.cur_pos += 1
                x, y = 0, 0
                for a, i in zip(args, args_is_float):
                    self.lookup(a, False)
                    is_float[a] = i
                    if i and y < 8:
                        self.add_favor(a, PhyReg(f'fa{y}'))
                        y += 1
                    elif not i and x < 8:
                        self.add_favor(a, PhyReg(f'a{x}'))
                        x += 1
                
                if not tail:
                    self.cur_pos += 1
                    x, y = 0, 0
                    for d, i in zip(dsts, dsts_is_float):
                        self.lookup(d, False)
                        is_float[d] = i
                        if i and y < 2:
                            self.add_favor(d, PhyReg(f'fa{y}'))
                            y += 1
                        elif not i and x < 2:
                            self.add_favor(d, PhyReg(f'a{x}'))
                            x += 1
            case MRet() | Nop() | MSimuHalt():
                ...
            case MBinaryImm(Id() as src, _imm, Id() as dst):
                self.lookup(src)
                self.lookup(dst)
                is_float[dst] = is_float[src] = False
            case instr:
                raise NotImplementedError(instr)

    def visit_check(self, instr: I, is_float: Mapping[Id, bool]):
        match instr:
            case MCopy(_is_float, src, dst):
                if isinstance(src, Id):
                    assert is_float[src] == _is_float
                else:
                    assert src.is_float() == _is_float
                if isinstance(dst, Id):
                    assert is_float[dst] == _is_float
                else:
                    assert dst.is_float() == _is_float

            case MLoadImm(_, Id() as dst) | MLui(_, Id() as dst) | MLuiHi(_, Id() as dst) | MCin(False, Id() as dst):
                assert not is_float[dst]
            case MLoadFZero(Id() as dst) | MCin(True, Id() as dst):
                assert is_float[dst]
            case MLoadFloatImm(_idx, Id() as dst):
                assert is_float[dst]
            case MLoad(_is_float, src, offset=_, dst=dst) | MLoadLo(_is_float, src, lo=_, dst=dst):
                if isinstance(src, Id):
                    assert not is_float[src]
                else:
                    assert not src.is_float()
                if isinstance(dst, Id):
                    assert is_float[dst] == _is_float
                else:
                    assert dst.is_float() == _is_float

            case MStore(_is_float, val, ptr, offset=_) | MStoreLo(_is_float, val, ptr, lo=_):
                if isinstance(val, Id):
                    assert is_float[val] == _is_float
                else:
                    assert val.is_float() == _is_float
                if isinstance(ptr, Id):
                    assert not is_float[ptr]
                else:
                    assert not ptr.is_float()
            case MOut(Id() as src) | MCout(False, Id() as src):
                assert not is_float[src]
            case MFCvtWS(Id() as s, Id() as w) | MFCvtSW(Id() as w, Id() as s) | MFMvWX(Id() as w, Id() as s) | MFMvXW(Id() as s, Id() as w):
                assert not is_float[w] and is_float[s]
            case MFMvWX(Id() as w, PhyReg('ft11')) | MFMvXW(PhyReg('ft11'), Id() as w):
                assert not is_float[w]
            case MUnary(Id() as src, Id() as dst):
                assert is_float[dst] == is_float[src] == isinstance(instr, (MFNeg, MFSqrt, MFAbs))
            case MFCmp(Id() as src1, Id() as src2, Id() as dst):
                assert is_float[src1] and is_float[src2] and not is_float[dst]
            case MBinary(Id() as src1, Id() as src2, Id() as dst):
                assert is_float[dst] == is_float[src1] == is_float[src2] == isinstance(instr, (MFAdd, MFSub, MFMul, MFDiv))
            case MIf(Id() | MEq() as cond, br_true, br_false, _is_float, dst):
                if isinstance(cond, Id):
                    assert not is_float[cond]
                else:
                    self.visit_check(cond, is_float)
                match br_true:
                    case list():
                        for i, b in enumerate(br_true):
                            assert isinstance(b, Id)
                            assert is_float[b] == _is_float[i]
                    case I():
                        self.visit_check(br_true, is_float)

                match br_false:
                    case list():
                        for i, b in enumerate(br_false):
                            assert isinstance(b, Id)
                            assert is_float[b] == _is_float[i]
                    case I():
                        self.visit_check(br_false, is_float)

                for i, d in enumerate(dst):
                    assert isinstance(d, Id)
                    assert is_float[d] == _is_float[i]
            case MSeq(instrs):
                for instr in instrs:
                    self.visit_check(instr, is_float)
            case MCall(MFunction(), args, args_is_float, tail, dsts, dsts_is_float) | MCallIntrinsic(_, args, args_is_float, tail, dsts, dsts_is_float):
                assert is_id_list(args) and is_id_list(dsts)
                assert all(is_float[a] == i for a, i in zip(args, args_is_float, strict=True))
                if not tail:
                    assert all(is_float[d] == i for d, i in zip(dsts, dsts_is_float, strict=True))
            case MRet() | Nop() | MSimuHalt():
                ...
            case MBinaryImm(Id() as src, _imm, Id() as dst):
                assert not is_float[dst] and not is_float[src]
            case instr:
                raise NotImplementedError(instr)
    # def visit_ssa(self, instr: I, writes: dict[Id, int], reads: dict[Id, int]):
    #     match instr:
    #         case MCopy(_is_float, src, dst):
    #             if isinstance(dst, Id):
    #                 writes[dst] = writes.get(dst, 0) + 1
    #             if isinstance(src, Id):
    #                 reads[src] = reads.get(src, 0) + 1
    #         case MLoadImm(_, Id() as dst) | MLui(_, Id() as dst) | MLuiHi(_, Id() as dst) \
    #             | MCin(_, Id() as dst) | MLoadFZero(Id() as dst) | MLoadFloatImm(_, _, Id() as dst):
    #             writes[dst] = writes.get(dst, 0) + 1
    #         case MLoad(_, src, _, dst) | MLoadLo(_, src, _, dst):
    #             if isinstance(dst, Id):
    #                 writes[dst] = writes.get(dst, 0) + 1
    #             if isinstance(src, Id):
    #                 reads[src] = reads.get(src, 0) + 1
    #         case MStore(_, val, ptr, _) | MStoreLo(_, val, ptr, _):
    #             if isinstance(val, Id):
    #                 reads[val] = reads.get(val, 0) + 1
    #             if isinstance(ptr, Id):
    #                 reads[ptr] = reads.get(ptr, 0) + 1
    #         case MOut(Id()):
    #             ...
    #         case MUnary(Id() as src, Id() as dst):
    #             writes[dst] = writes.get(dst, 0) + 1
    #             reads[src] = reads.get(src, 0) + 1
    #         case MBinary(Id() as src1, Id() as src2, Id() as dst):
    #             writes[dst] = writes.get(dst, 0) + 1
    #             reads[src1] = reads.get(src1, 0) + 1
    #             reads[src2] = reads.get(src2, 0) + 1
    #         case MIf(Id() as cond, br_true, br_false, _is_float, _dst):
    #             reads[cond] = reads.get(cond, 0) + 1
    #             match br_true:
    #                 case list():
    #                     for x in br_true:
    #                         if isinstance(x, Id):
    #                             reads[x] = reads.get(x, 0) + 1
    #                 case I():
    #                     self.visit_ssa(br_true, writes, reads)
                        

    def live(self, instr: I, live_in: set[Id]):
        match instr:
            case MCopy(_is_float, src, dst):
                if isinstance(dst, Id):
                    live_in.discard(dst)
                if isinstance(src, Id):
                    live_in.add(src)
            case MLoadImm(_, Id() as dst) | MLui(_, Id() as dst) | MLuiHi(_, Id() as dst) \
                | MCin(_, Id() as dst) | MLoadFZero(Id() as dst) | MLoadFloatImm(_, Id() as dst):
                live_in.discard(dst)
            case MLoad(_, src, _, dst) | MLoadLo(_, src, _, dst):
                if isinstance(dst, Id):
                    live_in.discard(dst)
                if isinstance(src, Id):
                    live_in.add(src)

            case MStore(_, val, ptr, _) | MStoreLo(_, val, ptr, _):
                if isinstance(val, Id):
                    live_in.add(val)
                if isinstance(ptr, Id):
                    live_in.add(ptr)

            case MOut(Id()) | MCout(_, Id()):
                ...
            case MUnary(src, dst):
                if isinstance(dst, Id):
                    live_in.discard(dst)
                if isinstance(src, Id):
                    live_in.add(src)
            case MBinary(Id() as src1, Id() as src2, Id() as dst):
                live_in.discard(dst)
                live_in.add(src1)
                live_in.add(src2)
            case MIf(Id() | MEq() as cond, br_true, br_false, _is_float, _dst):

                live_in1, live_in2 = set(live_in), set(live_in)
                match br_true:
                    case list():
                        for x in br_true:
                            if isinstance(x, Id):
                                live_in1.add(x)
                    case I():
                        self.live(br_true, live_in1)

                match br_false:
                    case list():
                        for x in br_false:
                            if isinstance(x, Id):
                                live_in2.add(x)
                    case I():
                        self.live(br_false, live_in2)

                live_in.clear()
                live_in.update(live_in1)
                live_in.update(live_in2)
                if isinstance(cond, Id):
                    live_in.add(cond)
                else:
                    self.live(cond, live_in)
            case MSeq(instrs):
                for instr in reversed(instrs):
                    self.live(instr, live_in)
            case MCall(MFunction(), args, _args_is_float, _tail, dsts, _dsts_is_float) | MCallIntrinsic(_, args, _args_is_float, _tail, dsts, _dsts_is_float):
                assert is_id_list(args) and is_id_list(dsts)
                live_in.difference_update(dsts)
                for x in live_in:
                    self.live_across_call[x] = True
                live_in.update(args)
            case MRet() | Nop() | MSimuHalt():
                ...
            case MBinaryImm(Id() as src, _imm, Id() as dst):
                live_in.discard(dst)
                live_in.add(src)

            case instr:
                raise NotImplementedError(instr)

    def check(self, register: dict[Id, PhyReg], location: dict[Id, StackSlot]):
        assert len(register) + len(location) == len(self.live_interval.maps[0])
        assert register.keys().isdisjoint(location.keys())
        for x, i in self.live_interval.maps[0].items():
            if x in register:
                for y, j in self.live_interval.maps[0].items():
                    if y in register and x != y and register[x] == register[y]:
                        assert i.disjoint(j)

    def linear_scan(self, mf: MFunction) -> tuple[dict[Id, PhyReg], dict[Id, StackSlot]]:  # , args: list[Id], formal_fvs: list[Id], rets: list[Id], instrs: list[I]
        return {}, {v: StackSlot(i) for i, v in enumerate(self.live_interval.maps[0])}
        active_int: list[tuple[Id, Interval]] = []
        active_float: list[tuple[Id, Interval]] = []
        free_int = \
            [PhyReg(f'a{i}') for i in range(LinearScan.As)][::-1] + \
            [PhyReg(f't{i}') for i in range(LinearScan.Ts)][::-1] + \
            [PhyReg(f's{i}') for i in range(LinearScan.Ss)][::-1]
        free_float = \
            [PhyReg(f'fa{i}') for i in range(LinearScan.Fas)][::-1] + \
            [PhyReg(f'ft{i}') for i in range(LinearScan.Fts)][::-1] + \
            [PhyReg(f'fs{i}') for i in range(LinearScan.Fss)][::-1]
        register: dict[Id, PhyReg] = {}
        location: dict[Id, StackSlot] = {}

        if self.live_across_call[mf.ra]:
            location[mf.ra] = StackSlot(len(location))
        else:
            register[mf.ra] = PhyReg('ra')

        for x, i in self.live_interval.maps[0].items():
            if x is mf.ra:
                continue
            if mf.is_float[x]:
                active = active_float
                free = free_float
            else:
                active = active_int
                free = free_int
                    
            removes: list[int] = []
            for k, (y, j) in enumerate(active):
                if j.end <= i.start:
                    removes.append(k)
                    if register[y] not in free:
                        free.append(register[y])
            for k in reversed(removes):
                del active[k]
            if not self.live_across_call[x]:
                if len(free) == 0:
                    spill_x, spill_i = max(active, key=lambda x: x[1].end)
                    if spill_i.end > i.end:
                        register[x] = register[spill_x]
                        location[spill_x] = StackSlot(len(location))
                        del register[spill_x]
                        active.remove((spill_x, spill_i))
                        active.append((x, i))
                    else:
                        location[x] = StackSlot(len(location))
                else:
                    try:
                        y = next((y for y in self.favor[x] if y in free))
                        register[x] = y
                        free.remove(y)
                    except (StopIteration, KeyError):
                        register[x] = free.pop()
                    active.append((x, i))
            else:
                favor_x = self.favor.get(x) or (
                    [PhyReg(f's{i}') for i in range(self.Ss)] if not mf.is_float[x] else [PhyReg(f'fs{i}') for i in range(self.Fss)])
                intersection = [y for y in favor_x if y in free]
                if not intersection:
                    active.sort(key=lambda x: x[1].end, reverse=True)
                    try:
                        spill_x, spill_i = next(((spill_x, spill_i) for spill_x, spill_i in active if
                                                 spill_i.end > i.end and register[spill_x] in favor_x))
                        register[x] = register[spill_x]
                        location[spill_x] = StackSlot(len(location))
                        del register[spill_x]
                        active.remove((spill_x, spill_i))
                        active.append((x, i))
                    except StopIteration:
                        location[x] = StackSlot(len(location))
                else:
                    register[x] = intersection[0]
                    free.remove(register[x])
                    active.append((x, i))

        self.check(register, location)
        return register, location


class AsmEmmiter:
    def __init__(self, builtins: dict[Id, Ty], globals: dict[Id, Ty], global_ids: Mapping[Id, tuple[Id, int]]):
        ...

    def visit_subst(self, instrs: Iterable[I], register: Mapping[Id, PhyReg], location: Mapping[Id, StackSlot], gp_offset: Mapping[Id, int], local_start: int, framesize: int) -> Iterable[I]:
        # def get_reg(x: Id | PhyReg):
        #     if isinstance(x, Id):
        #         return register[x]
        #     return x
        
        def get_reg_or_stackslot_or_global(x: Id | PhyReg):
            if isinstance(x, Id):
                try:
                    return register.get(x) or (PhyReg.sp, local_start - 4 * location[x] - 4)
                except KeyError:
                    return (PhyReg.gp, gp_offset[x])
            return x
        
        def copy(s: PhyReg | tuple[PhyReg, int], d: PhyReg | tuple[PhyReg, int], /):
            match s, d:
                case PhyReg(), PhyReg():
                    if s != d:
                        match s.is_float(), d.is_float():
                            case [True, True] | [False, False]:
                                yield MCopy(s.is_float(), s, d)
                            case True, False:
                                yield MFMvXW(s, d)
                            case _, _:
                                yield MFMvWX(s, d)
                case [base, offset], PhyReg():
                    match base:
                        case PhyReg():
                            yield MLoad(d.is_float(), base, offset, d)
                        case Id():
                            assert d.name != 't6'
                            yield MLuiHi(base, PhyReg('t6'))
                            if offset:
                                yield MAddi(PhyReg('t6'), offset, PhyReg('t6'))
                            yield MLoadLo(d.is_float(), PhyReg('t6'), base, d)
                case PhyReg(), [base, offset]:
                    match base:
                        case PhyReg():
                            yield MStore(s.is_float(), s, base, offset)
                        case Id():
                            assert s.name != 't6'
                            yield MLuiHi(base, PhyReg('t6'))
                            yield MStoreLo(s.is_float(), s, PhyReg('t6'), base)
                case [PhyReg() as base1, offset1], [PhyReg() as base2, offset2]:
                    if base1 != base2 or offset1 != offset2:
                        yield MLoad(True, base1, offset1, PhyReg('ft11'))
                        yield MStore(True, PhyReg('ft11'), base2, offset2)
                case _:
                    raise ValueError(s, d)
                
        def rearrange(xs: list[Id | PhyReg], xs_is_float: list[bool], maximum: int = 8, pass_argument: bool = True, /) -> Iterable[I]:
            pairs: list[tuple[PhyReg | tuple[PhyReg, int], PhyReg | tuple[PhyReg, int]]] = []
            i, j, k = 0, 0, -4 * (len(xs) - min(maximum, xs_is_float.count(False)) - min(maximum, xs_is_float.count(True)))
            for x, is_float in zip(xs, xs_is_float):
                rs = get_reg_or_stackslot_or_global(x)
                if not is_float and i < maximum:
                    rd = PhyReg(f'a{i}')
                    i += 1
                elif is_float and j < maximum:
                    rd = PhyReg(f'fa{j}')
                    j += 1
                else:
                    rd = (PhyReg.sp, k)
                    k += 4
                if rs != rd:
                    if pass_argument:
                        pairs.append((rs, rd))
                    else:
                        pairs.append((rd, rs))
            fsts = [fst for fst, snd in pairs if fst != snd]
            snds = [snd for fst, snd in pairs if fst != snd]
            
            if set(fsts).isdisjoint(snds):
                for s, d in pairs:
                    yield from copy(s, d)
            else:
                nodes = set(fsts + snds)
                ind = {k: 0 for k in nodes}
                for snd in snds:
                    ind[snd] += 1
                stack: list[tuple[PhyReg | tuple[PhyReg, int], PhyReg | tuple[PhyReg, int]]] = []
                while fsts:
                    i = 0
                    while i < len(fsts):
                        if ind[fsts[i]] == 0:
                            p = fsts[i], snds[i]
                            stack.append(p)
                            pairs.remove(p)
                            ind[snds[i]] -= 1
                            del fsts[i], snds[i]
                            break
                        i += 1
                    else:
                        if len(fsts) == 2:
                            assert fsts[0] == snds[1] and fsts[1] == snds[0]
                            stack.append((PhyReg('ft11'), fsts[0]))
                            stack.append((fsts[0], snds[0]))
                            stack.append((snds[0], PhyReg('ft11')))
                            break
                        else:
                            raise NotImplementedError()
                for s, d in reversed(stack):
                    yield from copy(s, d)
        scratch = (PhyReg('t0'), PhyReg('t1'), PhyReg('t2')), (PhyReg('ft0'), PhyReg('ft1'), PhyReg('ft2'))

        for instr in instrs:
            match instr:
                case MLoadImm(imm, dst):
                    d = get_reg_or_stackslot_or_global(dst)
                    match d:
                        case PhyReg():
                            yield MLoadImm(imm, d)
                        case _:
                            yield MLoadImm(imm, scratch[False][0])
                            yield from copy(scratch[False][0], d)
                case MLui(imm, dst):
                    d = get_reg_or_stackslot_or_global(dst)
                    match d:
                        case PhyReg():
                            yield MLui(imm, d)
                        case _:
                            yield MLui(imm, PhyReg('t6'))
                            yield from copy(PhyReg('t6'), d)

                case MLuiHi(label, dst):
                    raise NotImplementedError()
                    # d = get_reg_or_stackslot(dst)
                    # match d:
                    #     case PhyReg():
                    #         yield MLuiHi(label, d)
                    #     case _:
                    #         yield MLuiHi(label, PhyReg('t6'))
                    #         yield from copy(PhyReg('t6'), d)
                case MLoadFZero(dst):
                    yield from copy(PhyReg.zero, get_reg_or_stackslot_or_global(dst))
                case MLoadFloatImm(imm, dst):
                    l = MLoadFloatImm.float_table[imm]
                    yield from copy((PhyReg.gp, gp_offset[l]), get_reg_or_stackslot_or_global(dst))
                case MCopy(is_float, src, dst):
                    s = get_reg_or_stackslot_or_global(src)
                    d = get_reg_or_stackslot_or_global(dst)
                    yield from copy(s, d)
                case MOut(src):
                    match get_reg_or_stackslot_or_global(src):
                        case PhyReg() as s:
                            yield MOut(s)
                        case stackslot:
                            yield from copy(stackslot, scratch[False][0])
                            yield MOut(scratch[False][0])
                case MCout(is_float, src):
                    match get_reg_or_stackslot_or_global(src):
                        case PhyReg() as s:
                            yield MCout(is_float, s)
                        case stackslot:
                            yield from copy(stackslot, scratch[is_float][0])
                            yield MCout(is_float, scratch[is_float][0])
                case MCin(is_float, dst):
                    match get_reg_or_stackslot_or_global(dst):
                        case PhyReg() as d:
                            yield MCin(is_float, d)
                        case stackslot:
                            yield MCin(is_float, scratch[is_float][0])
                            yield from copy(scratch[is_float][0], stackslot)
                case MFMvXW(src, dst) | MFMvWX(src, dst):
                    s = get_reg_or_stackslot_or_global(src)
                    d = get_reg_or_stackslot_or_global(dst)
                    yield from copy(s, d)
                case MUnary(src, dst):
                    bs, bd = instr.is_float
                    yield from copy(get_reg_or_stackslot_or_global(src), scratch[bs][0])
                    yield replace(instr, src=scratch[bs][0], dst=scratch[bd][0])
                    yield from copy(scratch[bd][0], get_reg_or_stackslot_or_global(dst))
                case MBinaryImm(PhyReg(), _, PhyReg()):
                    yield instr
                case MBinaryImm(src, imm, dst):
                    yield from copy(get_reg_or_stackslot_or_global(src), scratch[False][0])
                    yield replace(instr, src=scratch[False][0], imm=imm, dst=scratch[False][0])
                    yield from copy(scratch[False][0], get_reg_or_stackslot_or_global(dst))
                case MBinary(src1, src2, dst):
                    yield from copy(get_reg_or_stackslot_or_global(src1), scratch[instr.is_float[0]][0])
                    yield from copy(get_reg_or_stackslot_or_global(src2), scratch[instr.is_float[1]][1])
                    yield replace(instr, src1=scratch[instr.is_float[0]][0], src2=scratch[instr.is_float[1]][1], dst=scratch[instr.is_float[2]][2])
                    yield from copy(scratch[instr.is_float[2]][2], get_reg_or_stackslot_or_global(dst))
                case MLoad(is_float, src, offset, dst):
                    s, d = get_reg_or_stackslot_or_global(src), get_reg_or_stackslot_or_global(dst)
                    match s:
                        case PhyReg('fp'):
                            offset += framesize
                            yield from copy((PhyReg.sp, offset), d)
                        case PhyReg():
                            yield from copy((s, offset), d)
                        case _:
                            assert not isinstance(d, PhyReg) or d.name != 't6'
                            yield from copy(s, PhyReg('t6'))
                            yield from copy((PhyReg('t6'), offset), d)

                case MLoadLo(is_float, src, lo, dst):
                    raise NotImplementedError()
                    # s, d = get_reg_or_stackslot(src), get_reg_or_stackslot(dst)
                    # match d:
                    #     case PhyReg():
                    #         yield MLoadLo(is_float, s, lo, d)
                    #     case int():
                    #         tmp = PhyReg('ft11')
                    #         yield MLoadLo(True, s, lo, tmp)
                    #         yield MStore(True, tmp, PhyReg.sp, d)

                case MStore(is_float, src, ptr, offset):
                    s, p = get_reg_or_stackslot_or_global(src), get_reg_or_stackslot_or_global(ptr)
                    match p:
                        case PhyReg('fp'):
                            offset += framesize
                            yield from copy(s, (PhyReg.sp, offset))
                        case PhyReg():
                            yield from copy(s, (p, offset))
                        case _:
                            assert not isinstance(p, PhyReg) or p.name != 't6'
                            yield from copy(p, PhyReg('t6'))
                            yield from copy(s, (PhyReg('t6'), offset))

                case MStoreLo(is_float, src, ptr, lo):
                    raise NotImplementedError()
                    # s, p = get_reg_or_stackslot(src), get_reg(ptr)
                    # match s:
                    #     case PhyReg():
                    #         yield MStoreLo(is_float, s, p, lo)
                    #     case int():
                    #         tmp = PhyReg('ft11')
                    #         yield MLoadLo(True, p, lo, tmp)
                    #         yield MStore(True, tmp, p, s)

                case MIf(cond, I() as br_true, I() as br_false, _is_float, _dst):

                    match list(self.visit_subst((br_true,), register, location, gp_offset, local_start, framesize)):
                        case []:
                            br_true_ = Nop()
                        case [instr]:
                            br_true_ = instr
                        case instrs:
                            br_true_ = MSeq(instrs)
                    match list(self.visit_subst((br_false,), register, location, gp_offset, local_start, framesize)):
                        case []:
                            br_false_ = Nop()
                        case [instr]:
                            br_false_ = instr
                        case instrs:
                            br_false_ = MSeq(instrs)

                    match cond:
                        case Id():
                            # c = register[cond]
                            yield from copy(get_reg_or_stackslot_or_global(cond), scratch[False][0])
                            yield MIf(scratch[False][0], br_true_, br_false_, _is_float, _dst)
                        case PhyReg():
                            yield MIf(cond, br_true_, br_false_, _is_float, _dst)
                        case MEq(src1, src2, dst):
                            s1, s2 = get_reg(src1), get_reg(src2)
                            yield MIf(MEq(s1, s2, dst), br_true_, br_false_, _is_float, _dst)
                        case MNeq(src1, src2, dst):
                            s1, s2 = get_reg(src1), get_reg(src2)
                            yield MIf(MNeq(s1, s2, dst), br_true_, br_false_, _is_float, _dst)
                        case _:
                            raise NotImplementedError(cond)
                case MSeq(seq):
                    seq_ = list(self.visit_subst(seq, register, location, gp_offset, local_start, framesize))
                    match seq_:
                        case []:
                            continue
                        case [i]:
                            yield i
                        case _:
                            yield MSeq(seq_)
                case MCall(MFunction(), args, args_is_float, tail, dsts, dsts_is_float) | MCallIntrinsic(_, args, args_is_float, tail, dsts, dsts_is_float):
                    yield from rearrange(args, args_is_float)
                    yield instr
                    yield from rearrange(dsts, dsts_is_float, 2, False)
                case MSimuHalt():
                    yield MLoadImm(-1, PhyReg('ra'))
                    yield MRet()
                case MRet() | MLabel() | MJump():
                    yield instr
                case Nop():
                    continue
                case _:
                    raise NotImplementedError(instr)

    def peephole(self, instrs: list[I]):
        from collections import deque
        q = deque[I]()
        res: list[I] = []

        for _i, instr in enumerate(instrs):
            q.append(instr)
            match q[0]:
                case MLoadImm(imm1, PhyReg() as d1):
                    if len(q) < 2:
                        continue
                    match q[1]:
                        case MSlli(PhyReg() as s1, imm2, PhyReg() as d2) if d1 == s1 == d2:
                            q.popleft()
                            q.popleft()
                            q.appendleft(MLoadImm(imm1 << imm2, d1))

                        case MAdd(PhyReg() as s1, PhyReg() as s2, PhyReg() as d2) if d1 == s1 or d1 == s2 and -2048 <= imm1 <= 2047:
                            if d1 == d2:
                                q.popleft()
                                q.popleft()
                                q.appendleft(MAddi(s2 if d1 == s1 else s1, imm1, d1))
                            else:
                                q[1] = MAddi(s2 if d1 == s1 else s1, imm1, d2)
                        case MSub(PhyReg() as s1, PhyReg() as s2, PhyReg() as d2) if d1 == s2 == d2 and -2048 <= imm1 <= 2047:
                            q.popleft()
                            q.popleft()
                            q.appendleft(MAddi(s1, -imm1, d1))
                        case MAddi(PhyReg() as s1, imm2, PhyReg() as d2) if d1 == s1 == d2:
                            q.popleft()
                            q.popleft()
                            q.appendleft(MLoadImm(imm1 + imm2, d1))
                        case MLoadImm(imm2, PhyReg() as d2) if d1 == d2:
                            q.popleft()
                        case _:
                            res.append(q.popleft())

                case MCopy(is_float1, PhyReg() as s, PhyReg() as d):
                    if s == d:
                        q.popleft()
                    elif len(q) > 1:
                        match q[1]:
                            case MCopy(_, PhyReg() as s1, PhyReg() as d1) if d == s1 and s != d1:
                                q[1] = MCopy(is_float1, s, d1)
                            case _:
                                res.append(q.popleft())
                case MAddi(PhyReg() as s, imm1, PhyReg() as d) if s == d and imm1 == 0:
                    q.popleft()
                case MIf(_, I() as br_true, I() as br_false, _, _) as mif:
                    q.popleft()
                    match br_true:
                        case MSeq():
                            self.peephole(br_true.instrs)
                            if not br_true.instrs:
                                mif.br_true = Nop()
                            elif len(br_true.instrs) == 1:
                                mif.br_true = br_true.instrs[0]
                        case _:
                            ...
                    match br_false:
                        case MSeq():
                            self.peephole(br_false.instrs)
                            if not br_false.instrs:
                                mif.br_false = Nop()
                            elif len(br_false.instrs) == 1:
                                mif.br_false = br_false.instrs[0]
                        case _:
                            ...
                    res.append(mif)
                # case MStore(_, PhyReg() as s, PhyReg() as p, offset):
                #     if len(q) > 1:
                #         match q[1]:
                #             case MStore(_, PhyReg() as s1, PhyReg() as p1, offset1) if p == p1 and offset == offset1:
                #                 if s != s1:
                #                     q[1] = MSeq([q[1], MCopy(False, s, s1)])
                #                 else:
                #                     q.popleft()
                #             case _:
                #                 res.append(q.popleft())

                case Nop() | MSeq([]):
                    q.popleft()
                case MSeq([i]):
                    q[0] = i
                case MSeq(ins):
                    q.popleft()
                    q.extendleft(ins)
                case _:
                    res.append(q.popleft())

        instrs.clear()
        instrs.extend(res)
        instrs.extend(q)

    def emit_asm(self, register: dict[Id, PhyReg], location: dict[Id, StackSlot], mf: MFunction, peephole: bool = False):
        framesize = 4 * len(location) + 4 * max(mf.n_words_pass_by_stack, mf.n_words_return_by_stack)
        local_start = 4 * len(location)
        while framesize & 15 != 0:
            framesize += 4
            local_start += 4
        instrs: list[str] = []
        instrs.append(f'.section .text')
        instrs.append(f'.type {mf.funct.dump_as_label()}, @function')
        instrs.append(f'.globl {mf.funct.dump_as_label()}')
        instrs.append(f'{mf.funct.dump_as_label()}:')
        # if isinstance(mf, MFunctionMain):
        #     instrs.append(f'    li gp, 0x10000')
        if framesize:
            instrs.append(f'    addi sp, sp, {-framesize}')

        def epilogue() -> Iterable[str]:
            if framesize:
                yield f'    addi sp, sp, {framesize}'
            yield f'    ret'

        preparation = list(self.visit_subst(mf.preparation, register, location, mf.global_var_gp_offset, local_start, framesize))
        gp_offset_int: dict[int, set[Id]] = {offset: set() for offset in mf.global_var_gp_offset.values()}
        gp_offset_int2: dict[int, tuple[Id, int]] = {offset: mf.global_var_addr.get(x, (x, 0)) for x, offset in mf.global_var_gp_offset.items()}

        for x, offset in mf.global_var_gp_offset.items():
            gp_offset_int[offset].add(x)

        if peephole:
            self.peephole(preparation)
        for instr in preparation:
            for res in self.emit_asm_instr(instr, epilogue, gp_offset_int, gp_offset_int2):
                instrs.append(f'{res} \t# {mf.funct}')

        # instrs.append(f'"{mf.funct}.func_begin":')
        body: list[I] = []
        for _i, b in enumerate(mf.body):
            for instr in self.visit_subst((b,), register, location, mf.global_var_gp_offset, local_start, framesize):
                body.append(instr)


        if peephole:
            self.peephole(body)
        for _i, instr in enumerate(body):
            for res in self.emit_asm_instr(instr, epilogue, gp_offset_int, gp_offset_int2):
                instrs.append(f'{res}')
        # instrs.append(f'{mf.funct}.func_end:')

        instrs.append('')
        return instrs

    def emit_asm_instr(self, instr: I, epilogue: Callable[[], Iterable[str]], gp_offset_int: Mapping[int, set[Id]], gp_offset_int2: Mapping[int, tuple[Id, int]]) -> Iterable[str]:
        tsuka = False
        allow_longjmp = True
        match instr:
            case MLoadImm(imm, PhyReg() as d):
                yield f'    li {d}, {int(imm)}'
            case MLoadFZero(PhyReg() as d):
                yield f'    fmv.w.x {d}, zero'
            case MLui(imm, PhyReg() as d):
                yield f'    lui {d}, {imm} # {hex(imm)}'
            case MLuiHi(label, PhyReg() as d):
                assert 0
                yield f'    lui {d}, %hi({label.dump_as_label()})'
            case MCopy(False, PhyReg() as s, PhyReg() as d):
                yield f'    mv {d}, {s}'
            case MCopy(True, PhyReg() as s, PhyReg() as d):
                yield f'    fmv.s {d}, {s}'
            case MOut(PhyReg() as s):
                if tsuka:
                    yield f'    out {s}'
                else:
                    assert s.name != 'a0'
                    yield f'    mv a0, {s}'
                    yield f'    call putchar'
            case MCin(False, PhyReg() as d):
                if tsuka:
                    yield f'    cin.int {d}'
                else:
                    yield f'    call read_int'
                    yield f'    mv {d}, a0'
            case MCin(True, PhyReg() as d):
                if tsuka:
                    yield f'    cin.float {d}'
                else:
                    yield f'    call read_float'
                    yield f'    fmv.s {d}, fa0'
            case MCout(False, PhyReg() as s):
                assert 0
                yield f'    cout.int {s}'
            case MCout(True, PhyReg() as s):
                assert 0
                yield f'    cout.float {s}'
            case MUnary(PhyReg() as s, PhyReg() as d):
                yield f'    {instr.opcode} {d}, {s}'
            case MBinaryImm(PhyReg() as s, imm, PhyReg() as d):
                yield f'    {instr.opcode} {d}, {s}, {imm}'
            case MBinary(PhyReg() as s1, PhyReg() as s2, PhyReg() as d):
                yield f'    {instr.opcode} {d}, {s1}, {s2}'
            case MTernary(PhyReg() as s1, PhyReg() as s2, PhyReg() as s3, PhyReg() as d):
                yield f'    {instr.opcode} {d}, {s1}, {s2}, {s3}'
            case MLoad(False, PhyReg() as s, offset, PhyReg() as d):
                if s.name == 'gp':
                    yield f"    lui {d}, %hi({gp_offset_int2[offset][0].dump_as_label()})"
                    if gp_offset_int2[offset][1]: yield f"    addi {d}, {d}, {4 * gp_offset_int2[offset][1]}"
                    yield f"    lw {d}, %lo({gp_offset_int2[offset][0]})({d})"
                    # yield f"    lw {d}, {offset}({s}) # {', '.join(map(str, gp_offset_int[offset]))}"
                elif offset > 2047 or offset < -2048:
                    yield f"    li t6, {offset}"
                    yield f"    add t6, {s}, t6"
                    yield f"    lw {d}, 0(t6)"
                else: 
                    yield f'    lw {d}, {offset}({s})'
            case MLoad(True, PhyReg() as s, offset, PhyReg() as d):
                if s.name == 'gp':
                    yield f"    lui t6, %hi({gp_offset_int2[offset][0].dump_as_label()})"
                    if gp_offset_int2[offset][1]: yield f"    addi t6, t6, {4 * gp_offset_int2[offset][1]}"
                    yield f"    flw {d}, %lo({gp_offset_int2[offset][0]})(t6)"
                    # yield f"    flw {d}, {offset}({s}) \t# {', '.join(map(str, gp_offset_int[offset]))}"
                elif offset > 2047 or offset < -2048:
                    yield f"    li t6, {offset}"
                    yield f"    add t6, {s}, t6"
                    yield f"    flw {d}, 0(t6)"
                else:
                    yield f'    flw {d}, {offset}({s})'
            case MLoadLo(False, PhyReg() as s, lo, PhyReg() as d):
                yield f'    lw {d}, %lo({lo.dump_as_label()})({s})'
            case MLoadLo(True, PhyReg() as s, lo, PhyReg() as d):
                yield f'    flw {d}, %lo({lo.dump_as_label()})({s})'
            case MStore(False, PhyReg() as src, PhyReg() as ptr, offset):
                if ptr.name == 'gp':
                    assert src.name != 't6'
                    yield f"    lui t6, %hi({gp_offset_int2[offset][0].dump_as_label()})"
                    if gp_offset_int2[offset][1]: yield f"    addi t6, t6, {4 * gp_offset_int2[offset][1]}"
                    yield f"    sw {src}, %lo({gp_offset_int2[offset][0].dump_as_label()})(t6)"
                    # yield f"    sw {src}, {offset}({ptr}) \t# {', '.join(map(str, gp_offset_int[offset]))}"
                elif offset > 2047 or offset < -2048:
                    yield f"    li t6, {offset}"
                    yield f"    add t6, {ptr}, t6"
                    yield f"    sw {src}, 0(t6)"
                else:
                    yield f'    sw {src}, {offset}({ptr})'
            case MStore(True, PhyReg() as src, PhyReg() as ptr, offset):
                if ptr.name == 'gp':
                    yield f"    lui t6, %hi({gp_offset_int2[offset][0].dump_as_label()})"
                    if gp_offset_int2[offset][1]: yield f"    addi t6, t6, {4 * gp_offset_int2[offset][1]}"
                    yield f"    fsw {src}, %lo({gp_offset_int2[offset][0].dump_as_label()})(t6)"
                    # yield f"    fsw {src}, {offset}({ptr}) \t# {', '.join(map(str, gp_offset_int[offset]))}"
                elif offset > 2047 or offset < -2048:
                    yield f"    li t6, {offset}"
                    yield f"    add t6, {ptr}, t6"
                    yield f"    fsw {src}, 0(t6)"
                else:
                    yield f'    fsw {src}, {offset}({ptr})'
            case MStoreLo(False, PhyReg() as src, PhyReg() as ptr, lo):
                yield f'    sw {src}, %lo({lo.dump_as_label()})({ptr})'
            case MStoreLo(True, PhyReg() as src, PhyReg() as ptr, lo):
                yield f'    fsw {src}, %lo({lo.dump_as_label()})({ptr})'

            case MIf(PhyReg() | MEq() | MNeq() as cond, I() as br_true, I() as br_false, _is_float, _dst):
                
                if not allow_longjmp:
                    else0 = Id('else0')
                    else_ = Id('else')
                    then_ = Id('then')
                    endif = Id('endif')
                    match cond:
                        case PhyReg():
                            yield f'    beqz {cond}, {else0.dump_as_label()}'
                        case MEq(PhyReg() as s1, PhyReg() as s2, _):
                            yield f'    bne {s1}, {s2}, {else0.dump_as_label()}'
                        case MNeq(PhyReg() as s1, PhyReg() as s2, _):
                            yield f'    beq {s1}, {s2}, {else0.dump_as_label()}'
                        case _:
                            raise NotImplementedError(cond)
                    yield f'    j {then_.dump_as_label()}'
                    yield f'{else0.dump_as_label()}:'
                    yield f'    j {else_.dump_as_label()}'
                    yield f'{then_.dump_as_label()}:'
                    yield from self.emit_asm_instr(br_true, epilogue, gp_offset_int, gp_offset_int2)
                    instrs_false = list(self.emit_asm_instr(br_false, epilogue, gp_offset_int, gp_offset_int2))
                    if instrs_false:
                        yield f'    j {endif.dump_as_label()}'
                    yield f'{else_.dump_as_label()}:'
                    yield from instrs_false
                    yield f'{endif.dump_as_label()}:'
                else:
                    else_ = Id('else')
                    endif = Id('endif')
                    match cond:
                        case PhyReg():
                            yield f'    beqz {cond}, {else_.dump_as_label()}'
                        case MEq(PhyReg() as s1, PhyReg() as s2, _):
                            yield f'    bne {s1}, {s2}, {else_.dump_as_label()}'
                        case MNeq(PhyReg() as s1, PhyReg() as s2, _):
                            yield f'    beq {s1}, {s2}, {else_.dump_as_label()}'
                        case _:
                            raise NotImplementedError(cond)
                    yield from self.emit_asm_instr(br_true, epilogue, gp_offset_int, gp_offset_int2)
                    instrs_false = list(self.emit_asm_instr(br_false, epilogue, gp_offset_int, gp_offset_int2))
                    if instrs_false:
                        yield f'    j {endif.dump_as_label()}'
                    yield f'{else_.dump_as_label()}:'
                    yield from instrs_false
                    yield f'{endif.dump_as_label()}:'
            case MSeq(instrs):
                for instr in instrs:
                    yield from self.emit_asm_instr(instr, epilogue, gp_offset_int, gp_offset_int2)
            case MCall(MFunction() as callee, _, _, _tail, _, _):
                yield f'    call {callee.funct.dump_as_label()}'
            case MCallIntrinsic(name, _tail, _is_float, _dst):
                yield f'    call {name}'
            case MRet():
                yield from epilogue()
            case MLabel(l):
                yield f'{l.dump_as_label()}:'
            case MJump(MLabel(l)):
                yield f'    j {l.dump_as_label()}'
            case Nop():
                ...
            case _:
                raise NotImplementedError(instr)
