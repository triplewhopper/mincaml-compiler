import enum
from typing import Tuple as Tup, Literal, Callable, List, TypeVar, Generic, ChainMap, Set, FrozenSet, Self, Protocol, \
    cast
from contextlib import contextmanager

from ty import *
from withbounds import WithBounds, merge
from collections import ChainMap
from infer import Monomorphization, Ty0Scheme
import syntax
import logging

logging.basicConfig(level=logging.INFO, format="%(asctime)s - %(name)s - %(levelname)s - %(message)s")
logger = logging.getLogger(__name__)

binary_operators = {'+', '+.', '-', '-.', '*.', '/.', '<', '<=', '>', '>=', '=', '<>'}
literal_binary = Literal['+', '+.', '-', '-.', '*.', '/.', '<', '<=', '>', '>=', '=', '<>']
unary_operators = ('-', '-.')
literal_unary = Literal['-', '-.']

U = TypeVar("U", bound=Ty)


class Id(ABC):
    __slots__ = []

    def acc_fv(self, acc: Set['LocalId']) -> None:
        ...

    def rm_fv(self, acc: set['LocalId']) -> None:
        ...

    @property
    @abstractmethod
    def bounds(self) -> Tup[int, int] | None:
        ...

    @abstractmethod
    def __eq__(self, other):
        ...

    @abstractmethod
    def __hash__(self):
        ...


class TmpId(Id):
    __slots__ = ["_val"]

    def __init__(self, idx: int):
        assert isinstance(idx, int) and idx >= 0
        self._val = idx

    @property
    def bounds(self) -> None:
        return None

    @property
    def val(self) -> int:
        return self._val

    def __str__(self):
        return f"__tmp_{self._val}"

    def __repr__(self):
        return f"TmpId({self._val})"

    def __eq__(self, other):
        if isinstance(other, TmpId):
            return self._val == other._val
        return NotImplemented

    def __hash__(self):
        return hash(self._val)


class LocalId(Id):
    __slots__ = ["_val", "_defn"]

    def __init__(self, val: WithBounds[str], defn: WithBounds[str]):
        assert isinstance(val, WithBounds)
        assert isinstance(val.val, str)
        assert isinstance(defn, WithBounds)
        assert isinstance(defn.val, str)
        assert val.val == defn.val
        self._val = val
        self._defn = defn

    def acc_fv(self, acc: Set['LocalId']) -> None:
        acc.add(self)

    def rm_fv(self, acc: set['LocalId']) -> None:
        acc.discard(self)

    @property
    def val(self) -> WithBounds[str]:
        return self._val

    @property
    def is_definition(self) -> bool:
        return self._val.bounds == self._defn.bounds

    def __eq__(self, other):
        if isinstance(other, LocalId):
            return self._val.val == other._val.val and self._defn.bounds == other._defn.bounds
        return NotImplemented

    def __hash__(self):
        return hash((self._val.val, self._defn.bounds))

    @property
    def bounds(self) -> Tup[int, int]:
        return self._val.bounds

    def __str__(self):
        return self._val.val

    def __repr__(self):
        if self.is_definition:
            return f"LocalId({self._val.val}@{self._val.bounds[0]}:{self._val.bounds[1]})"
        return f"LocalId({self._val.val}@{self._val.bounds[0]}:{self._val.bounds[1]} defined at {self._defn.bounds[0]}:{self._defn.bounds[1]})"


class GlobalId(Id):
    __slots__ = ["_val"]

    def __init__(self, val: WithBounds[str]):
        assert isinstance(val, WithBounds)
        assert isinstance(val.val, str)
        self._val = val

    def __repr__(self):
        return f"GlobalId({self._val.val}@{self._val.bounds[0]}:{self._val.bounds[1]})"

    def acc_fv(self, acc: set[WithBounds[str]]) -> None:
        ...

    def rm_fv(self, acc: set[WithBounds[str]]) -> None:
        ...

    def __eq__(self, other):
        if isinstance(other, GlobalId):
            return self._val == other._val
        return NotImplemented

    def __hash__(self):
        return hash(self._val)

    def __str__(self):
        return self._val.val

    @property
    def bounds(self) -> Tup[int, int]:
        return self._val.bounds

    @property
    def val(self) -> WithBounds[str]:
        return self._val


class KNormal:
    __slots__ = ["_bounds", "_typ"]

    def __init__(self, bounds: Tup[int, int], typ: U):
        assert isinstance(bounds, tuple) and len(bounds) == 2
        assert isinstance(typ, Ty)
        self._bounds = bounds
        self._typ = typ

    def get_type(self) -> U:
        return self._typ

    def accept(self, visitor: "KNormalVisitor"):
        return visitor.visit(self)

    @property
    def bounds(self) -> Tup[int, int]:
        return self._bounds


class Lit(KNormal):
    __slots__ = ["_val"]
    __match_args__ = ("val",)

    def __init__(self, val: WithBounds[int | float | bool | Literal["()"]]):
        assert isinstance(val, WithBounds)
        assert isinstance(val.val, (bool, int, float, str))
        assert not isinstance(val.val, str) or val.val == "()"
        match val.val:
            case bool():
                super().__init__(val.bounds, TyBool())
            case int():
                super().__init__(val.bounds, TyInt())
            case float():
                super().__init__(val.bounds, TyFloat())
            case "()":
                super().__init__(val.bounds, TyUnit())
            case _:
                raise NotImplementedError()
        self._val = val

    @staticmethod
    def unit_with_bounds(bounds: Tuple[int, int]) -> "Lit":
        return Lit(WithBounds(cast(Literal['()'], "()"), bounds))

    @property
    def val(self) -> WithBounds[int | float | bool | Literal["()"]]:
        return self._val

    def __str__(self):
        if self._val.val is True:
            return "true"
        if self._val.val is False:
            return "false"
        return str(self._val.val)


class Var(KNormal):
    __slots__ = ["_name"]
    __match_args__ = ("name",)

    def __init__(self, name: WithBounds[str], defn: WithBounds[str], typ: U):
        assert isinstance(name, WithBounds) and isinstance(name.val, str)
        assert isinstance(defn, WithBounds) and isinstance(defn.val, str)
        assert name.val == defn.val
        assert name.bounds != defn.bounds
        super().__init__(name.bounds, typ)
        self._name = LocalId(name, defn)

    def __str__(self):
        return self._name.val.val

    @property
    def name(self) -> LocalId:
        return self._name


class Ext(KNormal):
    __slots__ = ["_name"]
    __match_args__ = ("name",)

    def __init__(self, name: WithBounds[str], typ: U):
        assert isinstance(name, WithBounds) and isinstance(name.val, str)
        super().__init__(name.bounds, typ)
        self._name = GlobalId(name)

    def __str__(self):
        return self._name.val

    @property
    def name(self) -> GlobalId:
        return self._name


class Get(KNormal):
    __slots__ = ["_array", "_index"]
    __match_args__ = ("array", "index")

    def __init__(self, arr: Id, array: KNormal, idx: Id, index: KNormal):
        assert isinstance(arr, Id) and isinstance(idx, (TmpId, LocalId))
        array_type = array.get_type()
        index_type = index.get_type()
        assert isinstance(array_type, TyArray)
        assert isinstance(index_type, TyInt)
        super().__init__(merge(array.bounds, index.bounds), array_type.elem)
        self._array, self._index = arr, idx

    def __str__(self):
        return f"{self._array}.({self._index})"

    @property
    def array(self) -> Id:
        return self._array

    @property
    def index(self) -> LocalId | TmpId:
        return self._index


class Unary(KNormal):
    __slots__ = ["_op", "_e"]
    __match_args__ = ("op", "e")

    class OpKind(enum.Enum):
        I_NEG = enum.auto()
        F_NEG = enum.auto()

        def __str__(self) -> literal_unary:
            match self:
                case Unary.OpKind.I_NEG:
                    return "-"
                case Unary.OpKind.F_NEG:
                    return "-."
                case _:
                    raise NotImplementedError()

    def __init__(self, op: WithBounds[literal_unary], y: LocalId | TmpId, e: KNormal):
        assert isinstance(y, (LocalId, TmpId)) and isinstance(e, KNormal)
        assert isinstance(op, WithBounds) and op.val in unary_operators
        super(Unary, self).__init__(merge(op.bounds, e.bounds), e.get_type())
        match op.val, e.get_type():
            case '-', TyInt():
                op_kind = Unary.OpKind.I_NEG
            case ('-' | '-.'), TyFloat():
                op_kind = Unary.OpKind.F_NEG
            case _:
                raise NotImplementedError()
        self._op = WithBounds(op_kind, op.bounds)
        self._e: Id = y

    def __str__(self):
        return f"({str(self._op.val)} {self._e})"

    @property
    def op(self) -> OpKind:
        return self._op.val

    @property
    def e(self) -> Id:
        return self._e


class App(KNormal):
    __slots__ = ["_callee", "_args"]
    __match_args__ = ("callee", "args")
    __min_n_args = 1

    def __init__(self, f: Id, func: KNormal, *args: Tup[Id, KNormal]):
        assert isinstance(f, Id) and isinstance(func, KNormal)
        assert len(args) >= App.__min_n_args
        assert all(isinstance(x, Id) and isinstance(k, KNormal) for (x, k) in args)

        func_type = func.get_type()
        assert isinstance(func_type, TyFun)
        assert len(func_type.args) == len(args)
        assert all(kn.get_type() == t for (_, kn), t in zip(args, func_type.args))

        super(App, self).__init__(merge(func.bounds, *(kn.bounds for _, kn in args)), func_type.ret)
        self._callee, self._args = f, tuple(x for x, _ in args)

    def __str__(self):
        if not self._args:
            assert App.__min_n_args == 0
            return f"({self._callee} (*no args*))"
        return f"({self._callee} {' '.join(map(str, self._args))})"

    # def mask(self, mask: Tuple[bool, ...]) -> KNormal:
    #     assert len(mask) == len(self._args)
    #     return App(self._callee, self._args, *mask)
    @classmethod
    @contextmanager
    def relax_min_n_args(cls):
        old = cls.__min_n_args
        cls.__min_n_args = 0
        yield
        cls.__min_n_args = old

    @property
    def callee(self) -> Id:
        return self._callee

    @property
    def args(self) -> Tup[Id, ...]:
        return self._args


class Binary(KNormal):
    __slots__ = ["_op", "_e1", "_e2"]
    __match_args__ = ("op", "e1", "e2")

    class OpKind(enum.Enum):
        I_ADD = enum.auto()
        I_SUB = enum.auto()
        F_ADD = enum.auto()
        F_SUB = enum.auto()
        F_MUL = enum.auto()
        F_DIV = enum.auto()
        I_LT = enum.auto()
        F_LT = enum.auto()
        I_LE = enum.auto()
        F_LE = enum.auto()
        I_EQ = enum.auto()
        F_EQ = enum.auto()
        B_EQ = enum.auto()
        I_NEQ = enum.auto()
        F_NEQ = enum.auto()
        B_NEQ = enum.auto()
        I_GE = enum.auto()
        F_GE = enum.auto()
        I_GT = enum.auto()
        F_GT = enum.auto()

        # SEQ = enum.auto()

        def __str__(self) -> literal_binary:
            match self:
                case Binary.OpKind.I_ADD:
                    return "+"
                case Binary.OpKind.I_SUB:
                    return "-"
                case Binary.OpKind.F_ADD:
                    return "+."
                case Binary.OpKind.F_SUB:
                    return "-."
                case Binary.OpKind.F_MUL:
                    return "*."
                case Binary.OpKind.F_DIV:
                    return "/."
                case Binary.OpKind.I_LT | Binary.OpKind.F_LT:
                    return "<"
                case Binary.OpKind.I_LE | Binary.OpKind.F_LE:
                    return "<="
                case Binary.OpKind.I_EQ | Binary.OpKind.F_EQ | Binary.OpKind.B_EQ:
                    return "="
                case Binary.OpKind.I_NEQ | Binary.OpKind.F_NEQ | Binary.OpKind.B_NEQ:
                    return "<>"
                case Binary.OpKind.I_GE | Binary.OpKind.F_GE:
                    return ">="
                case Binary.OpKind.I_GT | Binary.OpKind.F_GT:
                    return ">"
                # case Binary.OpKind.SEQ:
                # return ";"
                case _:
                    raise NotImplementedError()

    def __init__(self, op: WithBounds[literal_binary], y1: Id, e1: KNormal, y2: Id, e2: KNormal):
        assert isinstance(e1, KNormal) and isinstance(e2, KNormal)
        assert isinstance(op, WithBounds) and op.val in binary_operators
        bounds = merge(op.bounds, e1.bounds, e2.bounds)
        # if op.val != ';':
        #     assert e1.get_type() is e2.get_type()
        if op.val in ('+', '-', '+.', '-.', '*.', '/.'):
            super(Binary, self).__init__(bounds, e2.get_type())
        elif op.val in ('<', '<=', '=', '>=', '>', '<>'):
            super(Binary, self).__init__(bounds, TyBool())
        else:
            raise NotImplementedError()
        match op.val, e1.get_type():
            case '+', TyInt():
                op_kind = Binary.OpKind.I_ADD
            case ('+' | '+.'), TyFloat():
                op_kind = Binary.OpKind.F_ADD
            case '-', TyInt():
                op_kind = Binary.OpKind.I_SUB
            case ('-' | '-.'), TyFloat():
                op_kind = Binary.OpKind.F_SUB
            case '+.', TyFloat():
                op_kind = Binary.OpKind.F_ADD
            case '-.', TyFloat():
                op_kind = Binary.OpKind.F_SUB
            case '*.', TyFloat():
                op_kind = Binary.OpKind.F_MUL
            case '/.', TyFloat():
                op_kind = Binary.OpKind.F_DIV
            case '<', TyInt():
                op_kind = Binary.OpKind.I_LT
            case '<', TyFloat():
                op_kind = Binary.OpKind.F_LT
            case '<=', TyInt():
                op_kind = Binary.OpKind.I_LE
            case '<=', TyFloat():
                op_kind = Binary.OpKind.F_LE
            case '=', TyInt():
                op_kind = Binary.OpKind.I_EQ
            case '=', TyFloat():
                op_kind = Binary.OpKind.F_EQ
            case '=', TyBool():
                op_kind = Binary.OpKind.B_EQ
            case '<>', TyInt():
                op_kind = Binary.OpKind.I_NEQ
            case '<>', TyFloat():
                op_kind = Binary.OpKind.F_NEQ
            case '<>', TyBool():
                op_kind = Binary.OpKind.B_NEQ
            case '>=', TyInt():
                op_kind = Binary.OpKind.I_GE
            case '>=', TyFloat():
                op_kind = Binary.OpKind.F_GE
            case '>', TyInt():
                op_kind = Binary.OpKind.I_GT
            case '>', TyFloat():
                op_kind = Binary.OpKind.F_GT
            # case ';', TyUnit():
            #     op_kind = Binary.OpKind.SEQ
            case _:
                raise NotImplementedError()
        self._op = WithBounds(op_kind, op.bounds)
        self._e1 = y1
        self._e2 = y2

    def __str__(self):
        return f"({self.e1} {str(self._op.val)} {self.e2})"

    @property
    def op(self) -> OpKind:
        return self._op.val

    @property
    def e1(self) -> Id:
        return self._e1

    @property
    def e2(self) -> Id:
        return self._e2


class Seq(KNormal):
    __slots__ = ["_es"]
    __match_args__ = ("es",)

    def __init__(self, *es: KNormal):
        assert len(es) >= 2
        assert all(isinstance(e, KNormal) for e in es)
        assert all(e.get_type() is TyUnit() for e in es[:-1])
        bounds = merge(*(e.bounds for e in es))
        super(Seq, self).__init__(bounds, es[-1].get_type())
        self._es = es

    def __str__(self):
        return f"({'; '.join(map(str, self.es))})"

    @property
    def es(self) -> Tup[KNormal, ...]:
        return self._es


class Tuple(KNormal):
    __slots__ = ["_elems"]

    def __init__(self, *elems: Tup[Id, KNormal]):
        """check elems is at least of length 2 at runtime"""
        assert all(isinstance(e, Id) and isinstance(elem, KNormal) for e, elem in elems)
        assert len(elems) >= 2
        bounds = merge(*(v.bounds for _, v in elems))
        typ = TyTuple([elem.get_type() for _, elem in elems])
        super(Tuple, self).__init__(bounds, typ)
        self._elems = tuple(x for x, _ in elems)

    def __str__(self):
        return f"({', '.join(map(str, self.elems))})"

    @property
    def elems(self) -> Tup[Id, ...]:
        return self._elems


class Put(KNormal):
    __slots__ = ["_array", "_index", "_value"]
    __match_args__ = ("array", "index", "value")

    def __init__(self, arr: Id, a: KNormal, idx: Id, i: KNormal, val: Id, v: KNormal):
        assert isinstance(arr, Id) and isinstance(idx, Id) and isinstance(val, Id)
        assert isinstance(a, KNormal) and isinstance(i, KNormal) and isinstance(v, KNormal)
        array_type = a.get_type()
        index_type = i.get_type()
        value_type = v.get_type()
        assert isinstance(array_type, TyArray)
        assert isinstance(index_type, TyInt)
        assert value_type == array_type.elem
        super().__init__(merge(a.bounds, i.bounds, v.bounds), TyUnit())
        self._array, self._index, self._value = arr, idx, val

    def __str__(self):
        return f"({self.array}.({self.index}) <- {self.value})"

    @property
    def array(self) -> Id:
        return self._array

    @property
    def index(self) -> Id:
        return self._index

    @property
    def value(self) -> Id:
        return self._value


class If(KNormal):
    __slots__ = ["_cond", "_br_true", "_br_false"]
    __match_args__ = ("cond", "br_true", "br_false")

    def __init__(self, cond: Tup[Id, KNormal], branch_true: KNormal, branch_false: KNormal, bounds: Tup[int, int]):
        cond_id, cond_expr = cond
        assert isinstance(cond_id, Id) and isinstance(cond_expr, KNormal)
        assert isinstance(branch_true, KNormal)
        assert isinstance(branch_false, KNormal)
        assert cond_expr.get_type() is TyBool()
        assert branch_true.get_type() == branch_false.get_type()
        super().__init__(bounds, branch_true.get_type())
        self._cond = cond_id
        self._br_true = branch_true
        self._br_false = branch_false

    def __str__(self):
        return f"(if {self.cond} then {self.br_true} else {self.br_false})"

    @property
    def cond(self) -> Id:
        return self._cond

    @property
    def br_true(self) -> KNormal:
        return self._br_true

    @property
    def br_false(self) -> KNormal:
        return self._br_false

    def br(self, b: bool) -> KNormal:
        return self._br_true if b else self._br_false


class Let(KNormal):
    __slots__ = ["_lhs", "_rhs", "_expr"]

    def __init__(self, lhs: LocalId | TmpId, rhs: KNormal, expr: KNormal, bounds: Tup[int, int]):
        """ when lhs is a string, it must match the regex "Let._regex_tmp", which indicates a temporary variable """
        assert isinstance(lhs, (LocalId, TmpId))
        assert isinstance(rhs, KNormal)
        assert isinstance(expr, KNormal)
        super(Let, self).__init__(bounds, expr.get_type())
        self._lhs = lhs
        self._rhs = rhs
        self._expr = expr

    @property
    def lhs(self) -> LocalId | TmpId:
        return self._lhs

    @property
    def rhs(self) -> KNormal:
        return self._rhs

    @property
    def expr(self) -> KNormal:
        return self._expr

    def __str__(self):
        if isinstance(self._lhs, TmpId):
            return f"(let {self._lhs}: {self._rhs.get_type()} = {self._rhs} in {self._expr})"
        return f"(let {self._lhs} = {self._rhs} in {self._expr})"


class LetTuple(KNormal):
    __slots__ = ["_xs", "_e1", "_e2"]

    def __init__(self, xs: Tup[WithBounds[str], ...], y: Tup[Id, KNormal], z: KNormal,
                 bounds: Tup[int, int]):
        """
        constraints:
        - value.get_type() is `t1 * ... * tn`
        - names == (x1, ..., xn)
        """
        assert isinstance(xs, tuple) and len(xs) >= 2
        assert all(isinstance(x, WithBounds) and isinstance(x.val, str) for x in xs)
        y, y_expr = y
        assert isinstance(y, Id) and isinstance(y_expr, KNormal)
        y_ty = y_expr.get_type()
        assert isinstance(y_ty, TyTuple) and len(y_ty.elems) == len(xs)
        assert isinstance(z, KNormal)
        super().__init__(bounds, z.get_type())
        self._xs = tuple(LocalId(x, x) for x in xs)
        self._e1 = y
        self._e2 = z

    @property
    def xs(self) -> Tup[LocalId, ...]:
        return self._xs

    @property
    def e1(self) -> Id:
        return self._e1

    @property
    def e2(self) -> KNormal:
        return self._e2

    def __str__(self):
        return f"(let ({', '.join(x.val.val for x in self._xs)}) = {self._e1} in {self._e2})"


class Function:
    __slots__ = ["_funct", "_formal_args", "_body", "_typ", "_bounds"]

    def __init__(self, funct: WithBounds[str], formal_args: Tup[WithBounds[str], ...],
                 body: KNormal, func_ty: TyFun, bounds: Tup[int, int]):
        assert isinstance(funct, WithBounds) and isinstance(funct.val, str)
        assert isinstance(formal_args, tuple) and isinstance(func_ty, TyFun)
        assert all(isinstance(x, WithBounds) and isinstance(x.val, str) for x in formal_args)
        assert len(formal_args) == len(func_ty.args)
        assert isinstance(body, KNormal) and body.get_type() == func_ty.ret
        self._funct = LocalId(funct, funct)
        self._formal_args = tuple(LocalId(x, x) for x in formal_args)
        self._body = body
        self._typ = func_ty
        self._bounds = bounds

    @property
    def funct(self) -> LocalId:
        return self._funct

    @property
    def body(self) -> KNormal:
        return self._body

    @property
    def formal_args(self) -> Tup[LocalId, ...]:
        return self._formal_args

    def get_type(self) -> TyFun:
        return self._typ

    def get_arg_type(self, i: int) -> Ty:
        return self._typ.args[i]

    def get_arg_name(self, i: int) -> LocalId:
        return self._formal_args[i]

    def get_n_args(self) -> int:
        return len(self._formal_args)

    def iter_args(self):
        return zip(self._formal_args, self._typ.args)

    @property
    def bounds(self) -> Tup[int, int]:
        return self._bounds

    def __repr__(self):
        return f"{self.__class__.__module__}.{self.__class__.__qualname__}({self._funct.val.val} @ {self._bounds[0]}: {self._bounds[1]})"


class LetRec(KNormal):
    __slots__ = ["_f", "_e"]

    def __init__(self, func: Function, expr: KNormal, bounds: Tup[int, int]):
        """
        let rec $name $arg1 ... $argn = $body in $expr
        """
        assert isinstance(func, Function)
        assert isinstance(expr, KNormal)
        assert self is not expr
        super(LetRec, self).__init__(bounds, expr.get_type())
        self._f = func
        self._e = expr

    @property
    def f(self) -> Function:
        return self._f

    @property
    def e(self) -> KNormal:
        return self._e

    def __str__(self):
        args = ' '.join(
            f"({self._f.get_arg_name(i)}: {self._f.get_arg_type(i)})" for i in range(self._f.get_n_args()))
        ret = self._f.get_type().ret
        return f"(let rec {self._f.funct} {args}: {ret} = {self._f.body} in {self._e})"


T = TypeVar("T", bound=KNormal)


class KNormalizer(syntax.NodeVisitor):
    def __init__(self, mono: Monomorphization, funcs: Dict[WithBounds[str], TyFun]):
        self._definitions = ChainMap[str, WithBounds[str]]()
        # self._ext = ext.copy()
        self._defns = ChainMap[str, WithBounds[str]]()
        self._counter = 0
        self._mono = mono
        self._known_ext_funcs: Dict[TyFun, Set[GlobalId]] = {}  # prepared for closure conversion
        self._known_ext_arrays: Dict[TyArray, Set[GlobalId]] = {}  # prepared for ir emission
        self._funcs = funcs.copy()

    @property
    def known_ext_funcs(self) -> Dict[TyFun, Set[GlobalId]]:
        """
        Set of external functions that should be converted to AppDir.
        Since functions must be fully applied in Min-Caml,
         all applications of external functions should be converted to AppDir.
        """
        return dict(self._known_ext_funcs)

    @property
    def known_ext_arrays(self) -> Dict[TyArray, Set[GlobalId]]:
        """
        Set of external arrays.
        """
        return dict(self._known_ext_arrays)

    def insert_let(self, kn1: KNormal, k: Callable[[Id], KNormal]) -> KNormal:
        if isinstance(kn1, Ext):
            return k(kn1.name)
        elif isinstance(kn1, Var):
            return k(kn1.name)
        x = TmpId(self._counter)
        self._counter += 1
        if len(s := str(kn1)) > 40:
            logger.info(f"generating fresh variable '%s' for %s ... %s", x, s[:20], s[-20:])
        else:
            logger.info(f"generating fresh variable '%s' for %s", x, s)
        kn2 = k(x)
        return Let(x, kn1, kn2, merge(kn1.bounds, kn2.bounds))

    def visit(self, node: syntax.Node) -> KNormal:
        x = super().visit(node)
        assert isinstance(x, KNormal)
        return x

    def visit_Lit(self, node: syntax.Lit) -> Lit:
        return Lit(node.get_val_with_bounds())

    def visit_Var(self, node: syntax.Var) -> Var | Ext:
        if not node.is_ext:
            return Var(node.name, self._defns[node.name.val], self._mono.visit(node.tyvar))
        else:
            ty = self._mono.visit(node.tyvar)
            if isinstance(ty, TyArray):
                res = Ext(node.name, ty)
                self._known_ext_arrays.setdefault(ty, set()).add(res.name)
                return res
            elif isinstance(ty, TyFun):
                res = Ext(node.name, ty)
                self._known_ext_funcs.setdefault(ty, set()).add(res.name)
                return res
            else:
                raise TypeError(f"{node.bounds}: external variable {node} does not have array type (got {ty})")

    def visit_Get(self, node: syntax.Get) -> KNormal:
        array = self.visit(node.e1)

        def k1(a: Id) -> KNormal:
            index = self.visit(node.e2)

            def k2(i: Id) -> KNormal:
                return Get(a, array, i, index)

            return self.insert_let(index, k2)

        return self.insert_let(array, k1)

    def visit_Unary(self, node: syntax.Unary) -> KNormal:
        e = self.visit(node.e)

        def k(x: Id) -> KNormal:
            return Unary(node.op, x, e)

        return self.insert_let(e, k)

    def visit_App(self, node: syntax.App) -> KNormal:
        callee = self.visit(node.callee)

        def k1(f: Id) -> KNormal:
            def bind(xs: List[Tup[Id, KNormal]], es: Tup[syntax.Node, ...], i: int) -> KNormal:
                if i == len(es):
                    return App(f, callee, *xs)
                kn0 = self.visit(es[i])

                def k2(x: Id) -> KNormal:
                    xs.append((x, kn0))
                    return bind(xs, es, i + 1)

                return self.insert_let(kn0, k2)

            return bind([], node.args, 0)

        return self.insert_let(callee, k1)

    def visit_Binary(self, node: syntax.Binary) -> KNormal:
        e1 = self.visit(node.e1)
        e2 = self.visit(node.e2)

        def k1(x1: Id) -> KNormal:
            def k2(x2: Id) -> KNormal:
                return Binary(node.op, x1, e1, x2, e2)

            return self.insert_let(e2, k2)

        return self.insert_let(e1, k1)

    def visit_Semi(self, node: syntax.Semi) -> KNormal:
        return Seq(*(self.visit(e) for e in node.es))

    def visit_Tuple(self, node: syntax.Tuple) -> KNormal:
        def bind(xs: List[Tup[Id, KNormal]], es: Tup[syntax.Node, ...], i: int) -> KNormal:
            if i == len(es):
                return Tuple(*xs)
            kn_i = self.visit(es[i])

            def k2(x: Id) -> KNormal:
                xs.append((x, kn_i))
                return bind(xs, es, i + 1)

            return self.insert_let(kn_i, k2)

        return bind([], node.es, 0)

    def visit_Put(self, node: syntax.Put) -> KNormal:
        array = self.visit(node.e1)

        def k1(a: Id) -> KNormal:
            index = self.visit(node.e2)

            def k2(i: Id) -> KNormal:
                value = self.visit(node.e3)

                def k3(v: Id) -> KNormal:
                    return Put(a, array, i, index, v, value)

                return self.insert_let(value, k3)

            return self.insert_let(index, k2)

        return self.insert_let(array, k1)

    def visit_If(self, node: syntax.If) -> KNormal:
        cond = self.visit(node.e1)

        def k1(c: Id) -> KNormal:
            br_true = self.visit(node.e2)
            br_false = self.visit(node.e3)
            return If((c, cond), br_true, br_false, node.bounds)

        return self.insert_let(cond, k1)

    def visit_Let(self, node: syntax.Let) -> KNormal:
        kn1 = self.visit(node.e1)
        # self._env = self._env.new_child({node.x.val: kn1.get_type()})
        self._defns = self._defns.new_child({node.x.val: node.x})
        kn2 = self.visit(node.e2)
        # self._env = self._env.parents
        self._defns = self._defns.parents
        return Let(LocalId(node.x, node.x), kn1, kn2, node.bounds)

    def visit_LetTuple(self, node: syntax.LetTuple) -> KNormal:
        kn1 = self.visit(node.e1)
        t1 = kn1.get_type()
        assert isinstance(t1, TyTuple)

        # xts: Dict[str, Ty] = {x.val: t for x, t in zip(node.xs, t1.elems)}

        def k1(y: Id) -> KNormal:
            # self._env = self._env.new_child(xts)
            self._defns = self._defns.new_child({x.val: x for x in node.xs})
            kn2 = self.visit(node.e2)
            # self._env = self._env.parents
            self._defns = self._defns.parents
            return LetTuple(node.xs, (y, kn1), kn2, node.bounds)

        return self.insert_let(kn1, k1)

    def visit_LetRec(self, node: syntax.LetRec) -> KNormal:
        assert node.f.funct in self._funcs
        func_type = self._funcs[node.f.funct]
        assert len(func_type.args) == len(node.f.formal_args)

        # m: Dict[str, Ty] = {node.f.funct.val: func_type}
        m_def: Dict[str, WithBounds[str]] = {node.f.funct.val: node.f.funct}
        # self._env = self._env.new_child(m)
        self._defns = self._defns.new_child(m_def)
        kn_e = self.visit(node.e)

        for x, t in zip(node.f.formal_args, func_type.args):
            # m[x.val] = t
            m_def[x.val] = x
        body = self.visit(node.f.body)

        kn_func = Function(node.f.funct, node.f.formal_args, body, func_type, node.f.bounds)
        # self._env = self._env.parents
        self._defns = self._defns.parents
        return LetRec(kn_func, kn_e, node.bounds)


class KNormalVisitor(ABC, Generic[T]):
    def visit(self, node: KNormal) -> T:
        return getattr(self, f"visit_{node.__class__.__name__}")(node)

    @abstractmethod
    def visit_Lit(self, node: Lit) -> T:
        pass

    @abstractmethod
    def visit_Var(self, node: Var) -> T:
        pass

    @abstractmethod
    def visit_Ext(self, node: Ext) -> T:
        pass

    @abstractmethod
    def visit_Get(self, node: Get) -> T:
        pass

    @abstractmethod
    def visit_Unary(self, node: Unary) -> T:
        pass

    @abstractmethod
    def visit_App(self, node: App) -> T:
        pass

    @abstractmethod
    def visit_Binary(self, node: Binary) -> T:
        pass

    @abstractmethod
    def visit_Seq(self, node: Seq) -> T:
        pass

    @abstractmethod
    def visit_Tuple(self, node: Tuple) -> T:
        pass

    @abstractmethod
    def visit_Put(self, node: Put) -> T:
        pass

    @abstractmethod
    def visit_If(self, node: If) -> T:
        pass

    @abstractmethod
    def visit_Let(self, node: Let) -> T:
        pass

    @abstractmethod
    def visit_LetTuple(self, node: LetTuple) -> T:
        pass

    @abstractmethod
    def visit_LetRec(self, node: LetRec) -> T:
        pass
