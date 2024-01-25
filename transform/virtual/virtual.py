import contextlib

from id import Id # , tmp_id_factory, LocalId, GlobalId, TmpId, SuffixId
import logging
from ty import Ty
from functools import lru_cache
from typing import Annotated, TypeVar, Protocol, Final
from collections.abc import Iterable
from collections import deque
# from transform.closure import IREmitter
from llvmlite.ir import IntType, FloatType, VoidType, FunctionType, PointerType, LiteralStructType, ArrayType, Type, \
    LabelType
import copy

logging.basicConfig(level=logging.INFO, format="%(asctime)s - %(name)s - %(levelname)s - %(message)s")
logger = logging.getLogger(__name__)


class PreludeTy:
    i32: Final = IntType(32)
    f32: Final = FloatType()
    i1: Final = IntType(1)
    i8: Final = IntType(8)
    void: Final = VoidType()


@lru_cache(maxsize=128)
def get_abi_size(ty: Type | Ty) -> Annotated[int, '4 byte aligned']:
    match ty:
        case Ty():
            from transform.closure import IREmitter
            return get_abi_size(IREmitter.get_ir_ty(ty))
        case PreludeTy.void:
            return 0
        case LiteralStructType(elements=elements):
            return sum(get_abi_size(x) for x in elements)
        case PreludeTy.i32 | PreludeTy.i8 | PreludeTy.i1 | PreludeTy.f32 | PointerType():
            return 4
        case _:
            raise NotImplementedError(ty)


# def determine_unary_bool_function(truth_table: tuple[bool, bool]):
#     def const_true(_: bool):
#         return True
#
#     def const_false(_: bool):
#         return False
#
#     def id(x: bool):
#         return x
#
#     def not_(x: bool):
#         return not x
#
#     match truth_table:
#         case True, True:
#             return const_true
#         case True, False:
#             return id
#         case False, True:
#             return not_
#         case False, False:
#             return const_false


def cls_ptr_to_func_ptr(ty: PointerType):
    assert isinstance(ty.pointee, FunctionType)
    return FunctionType(ty.pointee.return_type, ty.pointee.args[:-1]).as_pointer()


def assert_function_pointer(ty: Type):
    assert isinstance(ty, PointerType) and isinstance(ty.pointee, FunctionType)
    return ty.pointee


def _add__impl(x: 'Value', y: 'Value'):
    match x, y, x.typ, y.typ:
        case Imm(x), Imm(y), a, b if a == b:
            return Imm(x + y, a)
        case _, _, PreludeTy.i32, PreludeTy.i32:
            return Add(x, y)
        case _, _, PreludeTy.f32, PreludeTy.f32:
            return FAdd(x, y)
        case _, _, PointerType(), PreludeTy.i32:
            return GetElementPtr(x, y)

        case _:
            raise TypeError(x, y)


def _sub__impl(x: 'Value', y: 'Value'):
    match x, y, x.typ, y.typ:
        case Imm(x), Imm(y), a, b if a == b:
            return Imm(x - y, a)
        case _, _, PreludeTy.i32, PreludeTy.i32:
            return Sub(x, y)
        case _, _, PreludeTy.f32, PreludeTy.f32:
            return FSub(x, y)
        case _, _, PointerType(), PreludeTy.i32:
            return GetElementPtr(x, -y)
        case _:
            raise TypeError(x, y)


class Value:
    __slots__ = 'typ',

    def __init__(self, typ: Type):
        assert isinstance(typ, Type)
        self.typ = typ

    __add__ = _add__impl
    __sub__ = _sub__impl

    def __mul__(self, other):
        if self.typ == PreludeTy.i32:
            return Mul(self, other)
        return FMul(self, other)

    def __truediv__(self, other):
        return FDiv(self, other)

    def __floordiv__(self, other):
        return Div(self, other)

    def __call__(self, *args):
        match self.typ:
            case FunctionType(return_type=PreludeTy.void) | PointerType(
                pointee=FunctionType(return_type=PreludeTy.void)):
                return CallVoid(self, *args)
            case FunctionType(return_type=_) | PointerType(pointee=FunctionType(return_type=_)):
                return Call(self, *args)
            case _:
                raise TypeError(self.typ, args)

    def replace_all_uses(self, old: 'Value', new: 'Value'):
        raise NotImplementedError(self, old, new)


class Instr(Value):
    __slots__ = ()
    is_terminator = False

    def operands(self) -> 'Iterable[Value]':
        yield from ()

    def replace_all_uses(self, old: 'Value', new: 'Value'):
        ...


# def _getitem__impl(x: 'Imm | HasRd', *y: 'Imm | HasRd'):
#     if isinstance(x.typ, PointerType):
#         return Load(GetElementPtr(x, *y))
#     elif isinstance(x.typ, LiteralStructType):
#         return ExtractValue(x, *y)
#     raise ValueError(x.typ)
#
#
# def _setitem__impl(x: 'Imm | HasRd', *y: 'Imm | HasRd', z: 'Imm | HasRd'):
#     if isinstance(x.typ, PointerType):
#         return Store(z, GetElementPtr(x, *y))
#     elif isinstance(x.typ, LiteralStructType):
#         return InsertValue(x, z, *y)
#     raise ValueError(x.typ)


class HasRd(Instr):
    __slots__ = '_rd',

    def __init__(self, typ: Type, rd: Id | None, /):
        super(HasRd, self).__init__(typ)
        assert rd is None or isinstance(rd, (LocalId, TmpId, SuffixId))
        self._rd = rd or next(tmp_id_factory)

    @property
    def rd(self) -> Id:
        assert self._rd is not None
        return self._rd

    @rd.setter
    def rd(self, x: Id | None):
        if x is not None:
            if isinstance(x, Id):
                self._rd = x
            else:
                raise TypeError(x)


class _HasRs:
    __slots__ = ()

    def __init__(self, rs: Value, /):
        assert isinstance(rs, Value) and get_abi_size(rs.typ) > 0
        self.rs = rs

    def operands(self):
        yield self.rs

    def replace_all_uses(self, old: Value, new: Value):
        assert old.typ == new.typ
        if old is not new and self.rs is old:
            self.rs = new


# class _HasRsValue:
#     __slots__ = ()
#
#     def __init__(self, rs: Value, /):
#         assert isinstance(rs, Value) and get_abi_size(rs.typ) > 0
#         self.rs = rs


class Imm(Value):
    __slots__ = 'val',
    __match_args__ = 'val',
    _i32_pool: dict[int, 'Imm'] = {}
    _float_pool: dict[float, 'Imm'] = {}
    _i1_pool: dict[bool, 'Imm'] = {}

    def __new__(cls, *args, **kwargs):
        match args:
            case [bool() as val, PreludeTy.i1]:
                pool = cls._i1_pool
            case [float() as val, PreludeTy.f32]:
                pool = cls._float_pool
            case [int() as val, PreludeTy.i32]:
                pool = cls._i32_pool
            case _:
                return super(Imm, cls).__new__(cls)
        if val in pool:
            return pool[val]
        pool[val] = res = super(Imm, cls).__new__(cls)
        return res

    def __init__(self, val: bool | int | float, typ: Type | None = None):
        match val:
            case bool():
                assert typ is None or typ == PreludeTy.i1
                super(Imm, self).__init__(PreludeTy.i1)
            case float():
                assert typ is None or typ == PreludeTy.f32
                super(Imm, self).__init__(FloatType())
            case 0:
                assert typ is None or typ == PreludeTy.i32 or typ.is_pointer
                super(Imm, self).__init__(typ or PreludeTy.i32)
            case int():
                assert typ is None or typ == PreludeTy.i32
                super(Imm, self).__init__(PreludeTy.i32)
        self.val = val

    # def __neg__(self):
    #     match self.val, self.typ:
    #         case bool(), _:
    #             raise TypeError(self.val)
    #         case _, t if t == i32 or t == FloatType():
    #             return Imm(-self.val)
    #         case _:
    #             raise TypeError(self.val, self.typ)
    #
    # def __add__(self, other):
    #     match self.val, other:
    #         case [bool(), _] | [_, bool() | Imm(bool())]:
    #             return NotImplemented
    #         case [int(), int(v) | Imm(int(v))] | [float(), float(v) | Imm(float(v))] if not self.typ.is_pointer:
    #             return Imm(self.val + v)
    #         case _:
    #             return NotImplemented
    #
    # def __sub__(self, other):
    #     match self.val, other:
    #         case [bool(), _] | [_, bool() | Imm(bool())]:
    #             return NotImplemented
    #         case [int(), int(v) | Imm(int(v))] | [float(), float(v) | Imm(float(v))] if not self.typ.is_pointer:
    #             return Imm(self.val + v)
    #         case _:
    #             return NotImplemented
    #
    # def __mul__(self, other):
    #     match self.val, other:
    #         case [bool(), _] | [_, bool() | Imm(bool())]:
    #             return NotImplemented
    #         case [int(), int(v) | Imm(int(v))] | [float(), float(v) | Imm(float(v))] if not self.typ.is_pointer:
    #             return Imm(self.val + v)
    #         case _:
    #             return NotImplemented

    def __str__(self):
        return str(self.val)


class _HasRs1Proto(Protocol):
    rs1: Value


class _HasRs2Proto(Protocol):
    rs2: Value


class _HasRs1:
    __slots__ = ()

    def __init__(self: _HasRs1Proto, rs1: Value):
        assert isinstance(rs1, Value) and get_abi_size(rs1.typ) > 0
        self.rs1 = rs1


class _HasRs2:
    __slots__ = ()

    def __init__(self: _HasRs1Proto, rs2: Value):
        assert isinstance(rs2, Value) and get_abi_size(rs2.typ) > 0
        self.rs2 = rs2


def _dump(x: Value):
    if isinstance(x, Imm):
        if isinstance(x.val, float):
            import struct
            return repr(struct.unpack('f', struct.pack('f', x.val))[0])
        elif x.val is False:
            return 'false'
        elif x.val is True:
            return 'true'
        elif x.typ.is_pointer:
            assert x.val == 0
            return 'null'
        elif isinstance(x.val, int):
            return str(x.val)
        return str(x.val)
    if isinstance(x, (HasRd, Argument)):
        return x.rd.dump()
    if isinstance(x, Function):
        return x.funct.dump()
    if isinstance(x, GlobalVariable):
        return x.name.dump()
    raise NotImplementedError(x)

    #
    # class Reg(Value):
    #     __slots__ = 'name',
    # 
    #     def __init__(self, typ: Type, name: Id, /):
    #         assert isinstance(name, Id)
    #         super(Reg, self).__init__(typ)
    #         assert get_abi_size(typ) > 0
    #         self.name = name
    # 
    #     @staticmethod
    #     def new(typ: Type):
    #         return Reg(typ, next(tmp_id_factory))
    # 
    #     @staticmethod
    #     def from_ml_ty(typ: Ty, name: Id):
    #         return Reg(IREmitter.get_ir_ty(typ), name)

    # __add__ = _add__impl
    # __sub__ = _sub__impl
    #
    # def __getitem__(self, item: 'Reg | Imm | HasRd | tuple[Reg | Imm | HasRd, ...]'):
    #     if isinstance(item, tuple):
    #         return _getitem__impl(self, *item)
    #     return _getitem__impl(self, item)
    #
    # def __neg__(self):
    #     if self.typ == i32:
    #         return Neg(self)
    #     if self.typ == FloatType():
    #         return FNeg(self)
    #     raise ValueError(self.typ)
    # 
    # def __str__(self):
    #     return f"%{self.name}"


# class Label(Value):
#     def __init__(self, name: Id, /):
#         super(Label, self).__init__(VoidType())
#         self.name = name
#
#     def __repr__(self):
#         return f".{self.name.dump()}"
#
#     __str__ = __repr__


class GlobalValue(Value):
    __slots__ = ()

    def __init__(self, typ: Type, /):
        super(GlobalValue, self).__init__(typ.as_pointer())


class GlobalVariable(GlobalValue):
    __slots__ = 'name',

    def __init__(self, typ: Type, name: Id, /):
        super(GlobalVariable, self).__init__(typ)
        assert isinstance(name, Id)
        self.name = name

    def __str__(self):
        return self.name.dump()


class BasicBlock(Value):
    def __init__(self, parent: 'Function', /):
        super(BasicBlock, self).__init__(LabelType())
        self.parent = parent
        self.predecessors: list[BasicBlock] = []
        self.successors: list[BasicBlock] = []
        self.instructions: list[Instr] = []
        self._allow_append_phi = True

    @property
    def terminator(self) -> 'Branch | BranchCond | Ret | RetVoid | None':
        match self.instructions:
            case [*_, Branch() | BranchCond() | Ret() | RetVoid() as terminator]:
                return terminator
            case _:
                return None

    @terminator.setter
    def terminator(self, instr: 'Branch | BranchCond | Ret | RetVoid'):
        assert isinstance(instr, (Branch, BranchCond, Ret, RetVoid))
        if self.is_terminated:
            self.instructions[-1] = instr
        else:
            self.instructions.append(instr)

    @property
    def idx(self) -> int:
        return self.parent.idx(self)

    @property
    def n_phis(self) -> int:
        if len(self.instructions) == 0:
            return 0
        i = 0
        while isinstance(self.instructions[i], Phi):
            i += 1
        return i

    @property
    def is_terminated(self) -> bool:
        return self.terminator is not None

    def verify(self):
        if len(self.instructions) == 0:
            return True
        i = 0
        if self._allow_append_phi:
            return False
        while isinstance(self.instructions[i], Phi):
            i += 1
        while isinstance(self.instructions[i], Instr) and not self.instructions[i].is_terminator:
            i += 1
        if i == len(self.instructions) - 1 and self.instructions[i].is_terminator:
            return True
        return False

    def append(self, instr: Instr):
        assert isinstance(instr, Instr)
        if isinstance(instr, Phi):
            assert self._allow_append_phi
            assert len(instr.incoming) == len(self.predecessors)
            assert all(bb is bb1 for (_, bb), bb1 in zip(instr.incoming, self.predecessors))
        else:
            self._allow_append_phi = False
        assert not self.is_terminated
        self.instructions.append(instr)

    def __str__(self):
        buf = [f".LBB{self.idx}:"]
        if self.predecessors:
            buf[0] += f" ; predecessors: {', '.join(f'.LBB{bb.idx}' for bb in self.predecessors)}"
        else:
            buf[0] += ' ; no predecessors'
        for instr in self.instructions:
            buf.append(f"  {instr}")
        return '\n'.join(buf)

    def replace_all_uses(self, old: Value, new: Value):
        assert old.typ == new.typ
        if old is not new:
            if isinstance(old, Instr):
                i = 0
                while i < len(self.instructions):
                    if old is self.instructions[i]:
                        if isinstance(new, Instr):
                            self.instructions[i] = new
                            i += 1
                        else:
                            del self.instructions[i]
                    else:
                        self.instructions[i].replace_all_uses(old, new)
                        i += 1
            else:
                for instr in self.instructions:
                    instr.replace_all_uses(old, new)

    def topological_sort(self):
        if len(self.instructions) <= 1:
            return
        assert self.verify()
        ins = {i: set() for i in range(len(self.instructions))}
        outs = {i: set() for i in range(len(self.instructions))}
        for i, instr in enumerate(self.instructions):
            if not isinstance(instr, Phi):
                for op in instr.operands():
                    if isinstance(op, Instr):
                        try:
                            j = self.instructions.index(op)
                            ins[i].add(j)
                            outs[j].add(i)
                        except ValueError:
                            ...

        visited = [i for i in range(len(self.instructions)) if len(ins[i]) == 0]
        queue = deque(visited)
        # print(ins, outs)
        while queue:
            i = queue.popleft()
            for j in outs[i]:
                ins[j].remove(i)
                if not ins[j]:
                    queue.appendleft(j)
                    visited.append(j)
        assert len(visited) == len(self.instructions), 'cyclic dependency detected'
        self.instructions[:-1] = [self.instructions[i] for i in visited if i != len(self.instructions) - 1]
        assert self.verify()

    def __copy__(self, memodict={}):
        res = self.__class__(self.parent)
        res.instructions = copy.deepcopy(self.instructions)
        res._allow_append_phi = self._allow_append_phi
        return res
    #
    # def insert(self, idx: int, instr: Instr):
    #     assert isinstance(instr, Instr)
    #     assert not self.is_terminated
    #     if instr.is_terminator:
    #         self.terminator = instr
    #     self.instructions.insert(idx, instr)


class IRBuilder:
    def __init__(self, bb: BasicBlock):
        self._block = bb
        self._cursor = len(bb.instructions)

    @property
    def block(self) -> BasicBlock:
        """The current basic block."""
        return self._block

    @property
    def function(self) -> 'Function':
        """The current function."""
        return self._block.parent

    @contextlib.contextmanager
    def if_else(self, cond: Value):
        assert isinstance(cond, Value) and cond.typ == PreludeTy.i1
        bb_true = self.unsafe_append_basic_block()
        bb_false = self.unsafe_append_basic_block()
        bb_end = self.unsafe_append_basic_block()

        self.append(BranchCond(cond, bb_true, bb_false))

        @contextlib.contextmanager
        def on_branch(branch: BasicBlock, end: BasicBlock):
            old, self._block = self._block, branch
            old_cursor, self._cursor = self._cursor, len(branch.instructions)
            try:
                yield
            finally:
                if not self.block.is_terminated:
                    self.append(Branch(end))
                self._block, self._cursor = old, old_cursor

        try:
            yield on_branch(bb_true, bb_end), on_branch(bb_false, bb_end)
        finally:
            self._block, self._cursor = bb_end, len(bb_end.instructions)

    T = TypeVar('T', bound=Instr)

    def append(self, instr: T) -> T:
        assert isinstance(instr, Instr)
        if self._block.is_terminated:
            self._block = self.function.emplace_basic_block()
            self._cursor = 0
        self._block.append(instr)
        self._cursor += 1
        return instr

    def unsafe_append_basic_block(self) -> BasicBlock:
        return self.function.unsafe_append_basic_block()


class Argument(Value):
    __slots__ = 'rd',

    def __init__(self, typ: Type, name: Id, /):
        super(Argument, self).__init__(typ)
        self.rd = name

    def __repr__(self):
        return f"{self.typ} {self.rd.dump()}"


class Function(GlobalValue):
    def __init__(self, funct: Id, typ: FunctionType, args: tuple[Id | Argument, ...],
                 formal_fv: tuple[tuple[Id, Type], ...], /):
        assert len(args) == len(typ.args) and isinstance(typ, FunctionType)
        assert all(isinstance(arg, (Argument, LocalId, SuffixId)) for arg in args)
        args = [arg if isinstance(arg, Argument) else Argument(typ, arg) for arg, typ in zip(args, typ.args)]
        assert all(a.typ == t for a, t in zip(args, typ.args))

        assert not typ.var_arg or len(args) > 0 and len(formal_fv) == 0
        self.funct = funct
        self.funct.set_ir_prefix_as_global()
        if len(formal_fv) > 0:
            assert isinstance(funct, LocalId)
            self._fv_struct_ptr = Argument(
                LiteralStructType([t for _, t in formal_fv]).as_pointer(), funct.suffix('fv.struct.ptr'))
            self.args = (*args, self._fv_struct_ptr)
            typ = FunctionType(typ.return_type, [*typ.args, self._fv_struct_ptr.typ], typ.var_arg)
        else:
            self.args = tuple(args)
            self._fv_struct_ptr = None
        super(Function, self).__init__(typ)
        self.ftype = typ
        self._blocks: list[BasicBlock] = []
        self.formal_fv = formal_fv
        self.var_arg = typ.var_arg

        assert all(get_abi_size(t) > 0 for _, t in formal_fv)

    @property
    def fv_struct_ptr(self) -> Id | None:
        if self.formal_fv:
            return self._fv_struct_ptr.rd
        return None

    @property
    def fv_struct_ptr_typ(self) -> PointerType:
        assert len(self.formal_fv) > 0
        return self._fv_struct_ptr.typ

    @property
    def typ_as_closure_entry_erased(self):
        assert len(self.formal_fv) > 0
        return FunctionType(self.ftype.return_type, [*self.ftype.args[:-1], IntType(8).as_pointer()])

    @property
    def typ_lift_to_closure_entry(self):
        assert len(self.formal_fv) == 0
        return FunctionType(self.ftype.return_type, [*self.ftype.args, IntType(8).as_pointer()])

    @property
    def n_blocks(self) -> int:
        return len(self._blocks)

    def _good_entry_block(self) -> bool:
        if len(self._blocks) == 0:
            return True
        if not self._blocks[0].is_terminated:
            return False
        assert len(self._blocks[0].instructions) > 0
        if not any(isinstance(instr, Phi) for instr in self._blocks[0].instructions):
            return True

    def all_blocks_terminated(self) -> bool:
        assert self._good_entry_block()
        return all(block.is_terminated for block in self._blocks)

    def replace_all_uses(self, old: 'Value', new: 'Value'):
        assert old.typ == new.typ
        if old is not new:
            assert not isinstance(old, BasicBlock) and not isinstance(new, BasicBlock)
            # do not touch arguments

            for block in self._blocks:
                block.replace_all_uses(old, new)

    def update_predecessors_and_successors(self):
        assert self.all_blocks_terminated()
        for block in self._blocks:
            block.predecessors.clear()
            block.successors.clear()
        preds = [block.predecessors for block in self._blocks]
        succs = [block.successors for block in self._blocks]
        for i, block in enumerate(self._blocks):
            terminator = block.terminator
            if terminator is not None:
                if isinstance(terminator, Branch):
                    succs[i].append(terminator.target)
                    preds[terminator.target.idx].append(block)
                elif isinstance(terminator, BranchCond):
                    succs[i].append(terminator.on_true)
                    succs[i].append(terminator.on_false)
                    preds[terminator.on_true.idx].append(block)
                    preds[terminator.on_false.idx].append(block)
                else:
                    if self.ftype.return_type == PreludeTy.void:
                        assert isinstance(terminator, RetVoid)
                    else:
                        assert isinstance(terminator, Ret) and terminator.rs.typ == self.ftype.return_type

        for i, block in enumerate(self._blocks):
            assert len(block.predecessors) == len(set(block.predecessors))
            assert len(block.successors) == len(set(block.successors))

        assert all(self._blocks[0] not in block.successors for block in
                   self._blocks[1:]), 'entry block should have no successors'

    def remove_unreachable_blocks(self) -> int:
        # self.update_predecessors_and_successors()
        n = 0
        removes = []
        for block in self._blocks:
            if len(block.predecessors) == 0 and block is not self._blocks[0]:
                removes.append(block)
                for succ in block.successors:
                    succ.predecessors.remove(block)
                n += 1
        for block in removes:
            self._blocks.remove(block)
        return n

    def join_indirect_branches(self) -> int:
        """
        This function fuses indirect jumps due to basic block of length 1, i.e. a single branch instruction.
        Note that those target to a basic block beginning with PHI instruction will not be deleted.
        """
        fa = list(range(len(self._blocks)))

        def find(x: int):
            if fa[x] != x:
                x = fa[x] = find(fa[x])
            return x

        for i, block in enumerate(self._blocks):
            if len(block.instructions) == 1:
                t = block.terminator
                if isinstance(t, Branch) and not isinstance(t.target.instructions[0], Phi):
                    fa[i] = find(t.target.idx)

        fa2 = [self._blocks[find(x)] for x in fa]
        n = 0
        for i, block in enumerate(self._blocks):
            ter = block.terminator
            if isinstance(ter, Branch):
                assert len(block.successors) == 1
                target2 = fa2[ter.target.idx]
                if ter.target is not target2: n += 1
                ter.target = target2
            elif isinstance(ter, BranchCond):
                assert len(block.successors) == 2
                target3 = fa2[ter.on_true.idx]
                target4 = fa2[ter.on_false.idx]
                if ter.on_true is not target3: n += 1
                if ter.on_false is not target4: n += 1
                ter.on_true, ter.on_false = target3, target4
        if n:
            self.update_predecessors_and_successors()
            self.remove_unreachable_blocks()
        return n

    def has_critical_edges(self) -> bool:
        for block in self._blocks:
            if len(block.successors) > 1:
                for succ in block.successors:
                    if len(succ.predecessors) > 1:
                        return True
        return False

    def promote_return(self) -> bool:
        """
        transform those basic blocks like::

            .BBi:
                ...
                br label .BBj
            .BBj:
                ret %xx / ret void
        to::

            .BBi:
                ...
                ret %xx / ret void

        :return: bool, indicating if any return instruction is successfully promoted to its predecessor blocks.
        """
        flag = False
        for block in self._blocks:
            if isinstance(block.terminator, Branch):
                target = block.terminator.target
                match target.instructions:
                    case [Ret() | RetVoid()]:
                        flag = True
                        block.terminator = target.terminator
        if flag:
            self.update_predecessors_and_successors()
            self.remove_unreachable_blocks()
        return flag

    def simplify_gep(self):
        flag = False
        for bb in self._blocks:
            candidates: list[GetElementPtr] = []
            for instr in bb.instructions:
                if isinstance(instr, GetElementPtr) and len(instr.indices) == 1:
                    idx = instr.indices[0]
                    if isinstance(idx, Imm) and idx.val == 0:
                        flag = True
                        candidates.append(instr)
            for gep in candidates:
                bb.replace_all_uses(gep, gep.rs)
        return flag

    def topological_sort(self):
        # self.update_predecessors_and_successors()
        if not self._blocks:
            return
        # for bb in self._blocks:
        #     bb.topological_sort()

        visited = [False] * len(self._blocks)
        order = []

        def dfs(u: int):
            visited[u] = True
            for v in self._blocks[u].successors:
                idx = v.idx
                if not visited[idx]:
                    dfs(idx)
            order.append(u)

        dfs(0)
        assert len(order) == len(self._blocks)
        self._blocks = [self._blocks[i] for i in reversed(order)]

    def draw_cfg(self):
        import graphviz
        g = graphviz.Digraph(filename=f'cfg-{self.funct.dump()}', format='png')
        for block in self._blocks:
            g.node(str(block.idx), label=f'.LBB{block.idx}')
        for block in self._blocks:
            for succ in block.successors:
                g.edge(f'{block.idx}', f'{succ.idx}')
        print('rendering', g.render())

    # def inline(self):
    #     for block in self._blocks:
    #         for instr in block.instructions:
    #             if isinstance(instr, (Call, CallVoid)) and isinstance(instr.callee,
    #                                                                   Function) and instr.callee is not self:
    #                 ...

    def phi_elimination(self):
        # self.update_predecessors_and_successors()
        flag = False
        for block in self._blocks:
            match block.instructions:
                case [Phi() as phi, Ret() as ret] if ret.rs is phi:
                    flag = True
                    for j in range(len(phi.incoming)):
                        val, bb = phi.incoming[j]
                        bb.terminator = Ret(val)
        if flag:
            self.update_predecessors_and_successors()
            self.remove_unreachable_blocks()
            # if len(block.instructions) > 0:
            #     assert block.n_phis == 1, 'multiple PHI-nodes not supported yet'
            #     instr = block.instructions[0]
            #     while isinstance(instr, Phi):
            #         del block.instructions[0]
            #         flag = True
            #         assert len(instr.incoming) == len(block.predecessors)
            #         for j in range(len(instr.incoming)):
            #             val, bb = instr.incoming[j]
            #             assert len(bb.successors) == 1, 'critical edge detected'
            #             mov = Mov(val, rd=instr.rd.suffix(f'phi.{j}'))
            #             bb.instructions.insert(-1, mov)
            #
            #         instr = block.instructions[0]

        return flag

    def detect_tailcall(self):
        for block in self._blocks:
            match block.instructions:
                case [*_, Call() as call, Ret() as ret] if ret.rs is call:
                    call.tail = True
                case [*_, CallVoid() as call, RetVoid()]:
                    call.tail = True

    def __str__(self):
        buf = [
            'define ' if self._blocks else 'declare ',
            f"{self.ftype.return_type} {self.funct.dump()}(",
            ', '.join(map(str, self.args)),
            ')']
        if self._blocks:
            buf.append(' {\n')
            for bb in self._blocks:
                buf.append(str(bb))
                buf.append('\n')
            buf.append('}\n')
        return ''.join(buf)

    def emplace_basic_block(self) -> BasicBlock:
        bb = BasicBlock(self)
        if self._blocks and not self._blocks[-1].is_terminated:
            self._blocks[-1].append(Branch(bb))
        self._blocks.append(bb)
        return bb

    def unsafe_append_basic_block(self):
        bb = BasicBlock(self)
        self._blocks.append(bb)
        return bb

    def idx(self, bb: BasicBlock) -> int:
        return self._blocks.index(bb)

    def __call__(self, *args: Imm | HasRd):
        if self.ftype.return_type == VoidType():
            return CallVoid(self, *args)
        return Call(self, *args)

    def __copy__(self, memodict={}):
        res = self.__class__(self.funct, self.ftype, self.args, self.formal_fv)
        res._blocks = copy.deepcopy(self._blocks)
        return res

    def optimize(self):
        self.update_predecessors_and_successors()
        self.remove_unreachable_blocks()
        flag = False
        i = 0
        while True:
            flag = bool(self.join_indirect_branches()) or flag
            flag = self.phi_elimination() or flag
            flag = self.promote_return() or flag
            flag = self.simplify_gep() or flag
            if not flag:
                break
            else:
                flag = False
            i += 1

        self.topological_sort()
        self.detect_tailcall()

    def translate(self):
        sp = 0
        stack_pos: dict[LocalId, int] = {}
        for bb in self._blocks:
            for instr in bb.instructions:
                if isinstance(instr, Load) and isinstance(instr.rs, GetElementPtr):
                    del bb.instructions[bb.instructions.index(instr)]


# class LoadImm(HasRd):
#     __slots__ = 'imm',
#
#     def __init__(self, val: bool | int | float, /, *, rd: Id | None = None):
#         match val:
#             case bool():
#                 super(LoadImm, self).__init__(PreludeTy.i1, rd)
#             case float():
#                 super(LoadImm, self).__init__(PreludeTy.f32, rd)
#             case int():
#                 super(LoadImm, self).__init__(PreludeTy.i32, rd)
#             case _:
#                 raise TypeError(val)
#         self.imm = val
#
#     def __repr__(self):
#         return f"li {self.rd.dump()}, {self.imm}"


class Mov(HasRd, _HasRs):
    __slots__ = 'rs',
    operands = _HasRs.operands
    replace_all_uses = _HasRs.replace_all_uses

    def __init__(self, rs: Value, /, *, rd: Id | None = None):
        _HasRs.__init__(self, rs)
        HasRd.__init__(self, rs.typ, rd)

    def __repr__(self):
        return f"; {self.rd.dump()} = mov {self.rs.typ} {_dump(self.rs)}"


#
# class Mov(_HasRdRsSameType):
#     __slots__ = ()
#
#     def __init__(self, rs1: HasRd, rd: Id |  None = None):
#         HasRd.__init__(self, rd or rs1.typ)
#         _HasRs1.__init__(self, rs1)
#         assert get_abi_size(self.typ) == 4
#         assert self.typ == self.rs1.typ
#
#     def __repr__(self):
#         return f"{self.rd.dump()} = mov {self.rs1.typ} {self.rs1}"


class GetElementPtr(HasRd, _HasRs):
    __slots__ = 'rs', 'indices', 'gep_typs'

    def __init__(self, rs: Value, /, *indices: Value, rd: Id | None = None):
        _HasRs.__init__(self, rs)
        assert 1 <= len(indices) and all(isinstance(x, Value) for x in indices)
        assert isinstance(rs.typ, PointerType)
        last, typ = None, rs.typ
        gep_typs = []
        for idx in indices:
            assert idx.typ == PreludeTy.i32
            if isinstance(typ, LiteralStructType):
                assert isinstance(idx, Imm)
                assert 0 <= idx.val < len(typ.elements)
                last, typ = typ, typ.elements[idx.val]
            elif isinstance(typ, ArrayType):
                last, typ = typ, typ.element
            elif isinstance(typ, PointerType):
                last, typ = typ, typ.pointee
            else:
                raise TypeError('cannot index into', typ)
            gep_typs.append(typ)
        if isinstance(last, PointerType) and not isinstance(typ, PointerType):
            typ = last
        else:
            typ = typ.as_pointer()
        HasRd.__init__(self, typ, rd)
        self.indices = indices
        self.gep_typs = tuple(gep_typs)
        assert get_abi_size(self.typ) == 4

    def __repr__(self):
        indices = []
        for idx in self.indices:
            indices.append(f'{idx.typ} {_dump(idx)}')
        assert isinstance(self.rs.typ, PointerType)
        return f"{self.rd.dump()} = getelementptr {self.rs.typ.pointee}, {self.rs.typ} {self.rs.rd.dump()}, {', '.join(indices)}"

    def get_offset(self) -> int | None:
        if all(isinstance(x, Imm) for x in self.indices):
            typ = self.rs.typ
            i = iter(self.indices)
            assert isinstance(typ, PointerType)
            offset = get_abi_size(typ.pointee) * next(i).val
            typ = typ.pointee
            for idx in i:
                if isinstance(typ, LiteralStructType):
                    offset += sum(get_abi_size(x) for x in typ.elements[:idx.val])
                    typ = typ.elements[idx.val]
                elif isinstance(typ, ArrayType):
                    offset += idx.val * get_abi_size(typ.element)
                    typ = typ.element
                elif isinstance(typ, PointerType):
                    offset += idx.val * get_abi_size(typ.pointee)
                    typ = typ.pointee
                else:
                    assert False
            return offset
        return None

    def replace_all_uses(self, old: 'Value', new: 'Value'):
        assert old.typ == new.typ
        if old is self.rs:
            self.rs = new
        modified = [i for i, idx in enumerate(self.indices) if idx is old]
        if modified:
            self.indices = (self.indices[i] if i not in modified else new for i in range(len(self.indices)))

    def operands(self):
        yield self.rs
        yield from self.indices


class ExtractValue(HasRd, _HasRs):
    __slots__ = 'rs', 'indices'
    operands = _HasRs.operands
    replace_all_uses = _HasRs.replace_all_uses

    def __init__(self, rs: Value, /, *indices: int, rd: Id | None = None):
        _HasRs.__init__(self, rs)
        assert isinstance(rs.typ, LiteralStructType)
        assert len(indices) >= 1 and all(isinstance(x, int) for x in indices)
        typ = rs.typ
        for idx in indices:
            assert 0 <= idx < len(typ.elements)
            typ = typ.elements[idx]
        # assert get_abi_size(typ) == 4
        HasRd.__init__(self, typ, rd)
        self.indices = indices

    def __repr__(self):
        indices = []
        for idx in self.indices:
            indices.append(str(idx))
        return f"{self.rd.dump()} = extractvalue {self.rs.typ} {_dump(self.rs)}, {', '.join(indices)}; yields {self.typ}"


class InsertValue(HasRd, _HasRs):
    __slots__ = 'rs', 'val', 'indices'

    def __init__(self, rs: Value, /, val: Value, *indices: int, rd: Id | None = None):
        _HasRs.__init__(self, rs)
        assert isinstance(rs.typ, LiteralStructType)
        assert len(indices) >= 1 and all(isinstance(x, int) for x in indices)
        typ = rs.typ
        for idx in indices[:-1]:
            assert 0 <= idx < len(typ.elements)
            typ = typ.elements[idx]
        HasRd.__init__(self, typ, rd)
        # assert get_abi_size(typ) == 4
        self.val = val
        # self.val = val.rd if isinstance(val, HasRd) else val
        self.indices = indices

    def __repr__(self):
        indices = map(str, self.indices)
        return f"{self.rd.dump()} = insertvalue {self.rs.typ} {_dump(self.rs)}, {self.val.typ} {_dump(self.val)}, {', '.join(indices)}; yields {self.typ}"

    def replace_all_uses(self, old: 'Value', new: 'Value'):
        assert old.typ == new.typ
        if old is self.rs: self.rs = new
        if old is self.val: self.val = new

    def operands(self):
        yield self.rs
        yield self.val


class _Load(HasRd, _HasRs):
    __slots__ = 'rs',
    operands = _HasRs.operands
    replace_all_uses = _HasRs.replace_all_uses

    def __init__(self, rs: Value, rd: Id | None, /):
        _HasRs.__init__(self, rs)
        assert isinstance(rs.typ, PointerType)
        HasRd.__init__(self, rs.typ.pointee, rd)


class Load(_Load):
    __slots__ = ()

    def __init__(self, rs: Value, /, *, rd: Id | None = None):
        super(Load, self).__init__(rs, rd)
        assert get_abi_size(self.typ) > 0
        # assert get_abi_size(self.rs.typ) == 4

    def __repr__(self):
        return f"{self.rd.dump()} = load {self.typ}, {self.rs.typ} {_dump(self.rs)}"


class _Store(Instr):
    __slots__ = ('val', 'ptr')

    def __init__(self, val: Value, ptr: Value, /):
        Instr.__init__(self, PreludeTy.void)
        assert isinstance(val, Value) and isinstance(ptr, Value)
        assert isinstance(ptr.typ, PointerType) and ptr.typ.pointee == val.typ
        self.val = val
        self.ptr = ptr

    def replace_all_uses(self, old: 'Value', new: 'Value'):
        assert old.typ == new.typ
        if old is self.val: self.val = new
        if old is self.ptr: self.ptr = new

    def operands(self):
        yield self.val
        yield self.ptr


class Store(_Store):
    __slots__ = ()

    def __init__(self, val: Value, ptr: Value, /):
        super(Store, self).__init__(val, ptr)
        # assert get_abi_size(self.val.typ) == 4
        assert get_abi_size(self.ptr.typ) == 4

    def __repr__(self):
        return f"store {self.val.typ} {_dump(self.val)}, {self.ptr.typ} {_dump(self.ptr)}"


class BitCast(HasRd, _HasRs):
    __slots__ = 'rs',
    operands = _HasRs.operands
    replace_all_uses = _HasRs.replace_all_uses

    def __init__(self, rs: Value, typ: Type, /, *, rd: Id | None = None):
        _HasRs.__init__(self, rs)
        HasRd.__init__(self, typ, rd)
        assert get_abi_size(typ) == get_abi_size(rs.typ)

    def __repr__(self):
        return f"{self.rd.dump()} = bitcast {self.rs.typ} {_dump(self.rs)} to {self.typ}"


# struct_ty = LiteralStructType([i32, LiteralStructType([i32, i32])])
# ptr_ty = struct_ty.as_pointer()
# reg = Reg(struct_ty, next(tmp_id_factory))
# i = reg[1, 0]
# i.rd = Reg(i32, next(tmp_id_factory))
# print(i)

class _HasRs1Rs2:
    __slots__ = ()

    def __init__(self, rs1: Value, rs2: Value, /):
        assert isinstance(rs1, Value) and isinstance(rs2, Value)
        self.rs1 = rs1
        self.rs2 = rs2

    def operands(self):
        yield self.rs1
        yield self.rs2

    def replace_all_uses(self, old: 'Value', new: 'Value'):
        assert old.typ == new.typ
        if old is self.rs1: self.rs1 = new
        if old is self.rs2: self.rs2 = new


class _ICmp(HasRd, _HasRs1Rs2):
    __slots__ = 'rs1', 'rs2'
    op = ''
    operands = _HasRs1Rs2.operands
    replace_all_uses = _HasRs1Rs2.replace_all_uses

    def __init__(self, rs1: Value, rs2: Value, /, *, rd: Id | None = None):
        _HasRs1Rs2.__init__(self, rs1, rs2)
        assert rs1.typ == rs2.typ
        assert rs1.typ == PreludeTy.i32 or rs1.typ.is_pointer
        assert 0 < get_abi_size(rs1.typ) <= 4
        HasRd.__init__(self, PreludeTy.i1, rd)

    def __str__(self):
        assert self.op != ''
        return f"{self.rd.dump()} = icmp {self.op} {self.rs1.typ} {_dump(self.rs1)}, {_dump(self.rs2)}"


#
# class _ICmpi(HasRd, _HasRs1):
#     __slots__ = 'rs1', 'imm'
#     op = ''
#
#     def __init__(self, rs1: HasRd, imm: Imm, /, *, rd: Id | None = None):
#         _HasRs1.__init__(self, rs1)
#         assert rs1.typ == i32 or rs1.typ.is_pointer and imm.val == 0
#         assert 0 <= imm.val < 2 ** 5
#         HasRd.__init__(self, IntType(1), rd)
#         self.imm = imm
#
#     def __str__(self):
#         assert self.op != ''
#         return f"{self.rd.dump()} = icmp {self.op} {self.typ} {self.rs1.rd.dump()}, {self.imm.val}"
#
#
# class Eqi(_ICmpi):
#     __slots__ = ()
#     op = 'eq'


class Eq(_ICmp):
    __slots__ = ()
    op = 'eq'


class Neq(_ICmp):
    __slots__ = ()
    op = 'ne'


class Slt(_ICmp):
    __slots__ = ()
    op = 'slt'


class Sle(_ICmp):
    __slots__ = ()
    op = 'sle'


class Sgt(_ICmp):
    __slots__ = ()
    op = 'sgt'


class Sge(_ICmp):
    __slots__ = ()
    op = 'sge'


class _FCmp(HasRd, _HasRs1Rs2):
    __slots__ = 'rs1', 'rs2'
    op = ''
    operands = _HasRs1Rs2.operands
    replace_all_uses = _HasRs1Rs2.replace_all_uses

    def __init__(self, rs1: Value, rs2: Value, /, *, rd: Id | None = None):
        _HasRs1Rs2.__init__(self, rs1, rs2)
        assert rs1.typ == rs2.typ == FloatType()
        HasRd.__init__(self, PreludeTy.i1, rd)

    def __str__(self):
        assert self.op != ''
        return f"{self.rd.dump()} = fcmp fast {self.op} {self.rs1.typ} {_dump(self.rs1)}, {_dump(self.rs2)}"


class Oeq(_FCmp):
    __slots__ = ()

    op = 'oeq'


class Ogt(_FCmp):
    __slots__ = ()

    op = 'ogt'


class Oge(_FCmp):
    __slots__ = ()

    op = 'oge'


class Olt(_FCmp):
    __slots__ = ()

    op = 'olt'


class Ole(_FCmp):
    __slots__ = ()

    op = 'ole'


class One(_FCmp):
    __slots__ = ()

    op = 'one'


#
# class Addi(Arith):
#     rs1: Id
#     imm: int
#
#     def __str__(self):
#         return f"addi {self.rd.dump()}, {self.rs1}, {self.imm}"

class Arith2(HasRd, _HasRs1Rs2):
    __slots__ = 'rs1', 'rs2'
    biop = ''
    opearands = _HasRs1Rs2.operands
    replace_all_uses = _HasRs1Rs2.replace_all_uses

    def __init__(self, rs1: Value, rs2: Value, /, *, rd: Id | None = None):
        _HasRs1Rs2.__init__(self, rs1, rs2)
        assert rs1.typ == rs2.typ
        assert get_abi_size(rs1.typ) == 4
        HasRd.__init__(self, rs1.typ, rd)

    def __str__(self):
        assert self.biop != ''
        return f"{self.rd.dump()} = {self.biop} {self.typ} {_dump(self.rs1)}, {_dump(self.rs2)}"


class _AddSubMulDiv(Arith2):
    __slots__ = ()

    def __init__(self, rs1: Value, rs2: Value, /, *, rd: Id | None = None):
        super(_AddSubMulDiv, self).__init__(rs1, rs2, rd=rd)
        assert self.typ == PreludeTy.i32


class Add(_AddSubMulDiv):
    __slots__ = ()
    biop = 'add'


class Sub(_AddSubMulDiv):
    __slots__ = ()
    biop = 'sub'


class Mul(_AddSubMulDiv):
    __slots__ = ()
    biop = 'mul'


class Div(_AddSubMulDiv):
    __slots__ = ()
    biop = 'sdiv'


class _FAddSubMulDiv(Arith2):
    __slots__ = ()

    def __init__(self, rs1: Value, rs2: Value, /, *, rd: Id | None = None):
        super(_FAddSubMulDiv, self).__init__(rs1, rs2, rd=rd)
        assert rs1.typ == rs2.typ == PreludeTy.f32


class FAdd(_FAddSubMulDiv):
    __slots__ = ()
    biop = 'fadd'


class FSub(_FAddSubMulDiv):
    __slots__ = ()
    biop = 'fsub'


class FMul(_FAddSubMulDiv):
    __slots__ = ()
    biop = 'fmul'


class FDiv(_FAddSubMulDiv):
    __slots__ = ()
    biop = 'fdiv'


class Arith1(HasRd, _HasRs):
    __slots__ = 'rs',
    uop = ''
    operands = _HasRs.operands
    replace_all_uses = _HasRs.replace_all_uses

    def __init__(self, rs: Value, rd: Id | None = None):
        HasRd.__init__(self, rs.typ, rd)
        _HasRs.__init__(self, rs)

    def __str__(self):
        assert self.uop != ''
        return f"{self.rd.dump()} = {self.uop} {self.typ} {_dump(self.rs)}"


class Neg(Arith1):
    __slots__ = ()
    uop = 'neg'

    def __init__(self, rs2: Value, /, *, rd: Id | None = None):
        super(Neg, self).__init__(rs2, rd)
        assert self.typ == PreludeTy.i32

    def __str__(self):
        return f"{self.rd.dump()} = sub {self.typ} 0, {_dump(self.rs)}"


class FNeg(Arith1):
    __slots__ = ()
    uop = 'fneg'

    def __init__(self, rs2: Value, /, *, rd: Id | None = None):
        super(FNeg, self).__init__(rs2, rd)
        assert self.typ == PreludeTy.f32


#
# class Nop(Instr):
#     __slots__ = ()
#
#     def __init__(self):
#         super(Nop, self).__init__(VoidType())
#
#     def __str__(self):
#         return f"nop"


# def is_closure_typ(typ: Type) -> bool:
#     if isinstance(typ, LiteralStructType) and len(typ.elements) == 2:
#         cls_ptr, fv_struct_ptr = typ.elements
#         if isinstance(cls_ptr, PointerType) and isinstance(cls_ptr.pointee, FunctionType):
#             if len(cls_ptr.pointee.args) >= 1 and cls_ptr.pointee.args[-1] == i8.as_pointer():
#                 if fv_struct_ptr == IntType(8).as_pointer():
#                     return True
#     return False


class Call(HasRd):
    __slots__ = 'callee', 'args', 'tail'

    def __init__(self, callee: Value, *args: Value, rd: Id | None = None):
        ftype = assert_function_pointer(callee.typ)
        assert ftype.return_type != PreludeTy.void
        assert all(isinstance(x, Value) for x in args) and len(ftype.args) == len(args)
        assert all(x == arg.typ for x, arg in zip(ftype.args, args))
        super(Call, self).__init__(ftype.return_type, rd)
        self.callee = callee
        self.args = tuple(args)
        self.tail = False

        # assert get_abi_size(self.typ) in (4, 8)

    def __str__(self):
        args = []
        for arg in self.args:
            args.append(f'{arg.typ} {_dump(arg)}')
        callee = _dump(self.callee)
        tail = 'tail ' if self.tail else ''
        return f"{self.rd.dump()} = {tail}call {self.typ} {callee}({', '.join(args)})"

    def replace_all_uses(self, old: 'Value', new: 'Value'):
        assert old.typ == new.typ
        if old is self.callee: self.callee = new
        modified = [i for i, arg in enumerate(self.args) if arg is old]
        if modified:
            self.args = (self.args[i] if i not in modified else new for i in range(len(self.args)))

    def operands(self):
        yield self.callee
        yield from self.args


class CallVoid(Instr):
    __slots__ = 'callee', 'args', 'tail'

    def __init__(self, callee: Value, *args: Value):
        assert isinstance(callee, Value)
        ftype = assert_function_pointer(callee.typ)
        assert len(ftype.args) == len(args) and all(arg.typ == t for arg, t in zip(args, ftype.args))
        assert ftype.return_type == PreludeTy.void
        super(CallVoid, self).__init__(PreludeTy.void)
        self.callee = callee
        self.args = args
        self.tail = False

    def __str__(self):
        tail = 'tail ' if self.tail else ''
        args = [f'{arg.typ} {_dump(arg)}' for arg in self.args]
        return f"{tail}call void {_dump(self.callee)}({', '.join(args)})"

    operands = Call.operands
    replace_all_uses = Call.replace_all_uses


class Ret(HasRd, _HasRs):
    __slots__ = 'rs',
    is_terminator = True
    operands = _HasRs.operands
    replace_all_uses = _HasRs.replace_all_uses

    def __init__(self, rs: Value, /, *, rd: Id | None = None):
        HasRd.__init__(self, rs.typ, rd)
        _HasRs.__init__(self, rs)
        assert rs.typ != PreludeTy.void

    def __str__(self):
        return f"ret {self.rs.typ} {_dump(self.rs)}"


class RetVoid(Instr):
    __slots__ = ()
    is_terminator = True

    def __init__(self):
        super(RetVoid, self).__init__(PreludeTy.void)

    def __str__(self):
        return "ret void"


class Calloc(HasRd):
    __slots__ = 'num', 'size'

    def __init__(self, num: Value, size: Value, /, *,
                 rd: Id | None = None):
        assert isinstance(num, Value) and isinstance(size, Value)
        HasRd.__init__(self, PreludeTy.i8.as_pointer(), rd)
        assert num.typ == PreludeTy.i32 and size.typ == PreludeTy.i32
        self.num = num
        self.size = size

    def __str__(self):
        return f"{self.rd.dump()} = call {self.typ}(i32, i32) @lib.calloc(i32 {_dump(self.num)}, i32 {_dump(self.size)})"

    def operands(self):
        yield self.num
        yield self.size

    def replace_all_uses(self, old: 'Value', new: 'Value'):
        assert old.typ == new.typ
        if old is self.num: self.num = new
        if old is self.size: self.size = new


class Alloca(HasRd):
    __slots__ = ()

    def __init__(self, typ: Type, /, *, rd: Id | None = None):
        HasRd.__init__(self, typ.as_pointer(), rd)

    def __str__(self):
        return f"{self.rd.dump()} = alloca {self.typ.pointee} ; yields {self.typ}"


class Phi(HasRd):
    __slots__ = 'incoming',

    def __init__(self, typ: Type, /, *, rd: Id | None = None):
        super(Phi, self).__init__(typ, rd)
        self.incoming: list[tuple[Value, BasicBlock]] = []

    def add_incoming(self, v: Value, bb: BasicBlock):
        assert isinstance(v, Value) and isinstance(bb, BasicBlock)
        assert v.typ == self.typ
        self.incoming.append((v, bb))

    def __str__(self):
        args = []
        for r, bb in self.incoming:
            args.append(f'[{_dump(r)}, %.LBB{bb.idx}]')
        return f"{self.rd.dump()} = phi {self.typ} {', '.join(args)}"

    def replace_all_uses(self, old: 'Value', new: 'Value'):
        assert old.typ == new.typ
        modified = [i for i, (v, _) in enumerate(self.incoming) if v is old]
        if modified:
            self.incoming = [(v if i not in modified else new, bb) for i, (v, bb) in enumerate(self.incoming)]


#
# class LoadAddr(Instr):
#     rd: Reg = dataclasses.field(init=False)
#     symbol: Label
#
#     def __post_init__(self):
#         object.__setattr__(self, 'rd', Reg(next(tmp_id_factory), TyInt()))
#
#     def __repr__(self):
#         return f"la {self.rd.dump()}, {self.symbol}"

class BranchCond(Instr):
    __slots__ = 'cond', 'on_true', 'on_false'
    is_terminator = True

    def __init__(self, cond: Value, on_true: BasicBlock, on_false: BasicBlock):
        assert isinstance(cond, Value) and cond.typ == IntType(1)
        assert isinstance(on_true, BasicBlock) and isinstance(on_false, BasicBlock)
        super(BranchCond, self).__init__(VoidType())
        self.cond = cond
        self.on_true = on_true
        self.on_false = on_false

    def __repr__(self):
        return f"br {self.cond.typ} {_dump(self.cond)}, label %.LBB{self.on_true.idx}, label %.LBB{self.on_false.idx}"

    def operands(self):
        yield self.cond

    def replace_all_uses(self, old: 'Value', new: 'Value'):
        assert old.typ == new.typ
        if old is self.cond: self.cond = new


class Branch(Instr):
    __slots__ = 'target'
    is_terminator = True

    def __init__(self, target: BasicBlock):
        assert isinstance(target, BasicBlock)
        super(Branch, self).__init__(VoidType())
        self.target = target

    def __repr__(self):
        return f"br label %.LBB{self.target.idx}"
