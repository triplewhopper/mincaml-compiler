import email.generator
import inspect
from typing import Set, FrozenSet, TypeVar, Tuple as Tup, List, Generic, Callable, Self, Iterable, Type, Dict
from abc import ABC, abstractmethod
from collections import ChainMap

from withbounds import WithBounds
import ty
import knormal as K
import logging

logging.basicConfig(level=logging.INFO, format="%(asctime)s - %(name)s - %(levelname)s - %(message)s")
logger = logging.getLogger(__name__)


class Cls:
    __slots__ = ["_entry", "_actual_fv"]

    def __init__(self, entry: 'Function', actual_fv: Tup[K.LocalId, ...]):
        assert isinstance(entry, Function) and isinstance(actual_fv, tuple)
        assert all(isinstance(x, K.LocalId) for x in actual_fv)
        assert len(entry.formal_fv) == len(actual_fv)
        self._entry = entry
        self._actual_fv = actual_fv

    @property
    def entry(self) -> 'Function':
        return self._entry

    @property
    def actual_fv(self) -> Tup[K.LocalId, ...]:
        return self._actual_fv


class Function:
    __slots__ = ["_f", "_body", "_formal_fv"]

    def __init__(self, f: K.Function, body: 'Exp', formal_fv: Tup[Tup[K.LocalId, ty.Ty], ...]):
        assert isinstance(f, K.Function) and isinstance(body, Exp) and isinstance(formal_fv, tuple)
        for (v, t) in formal_fv:
            assert isinstance(v, K.LocalId) and isinstance(t, ty.Ty)
        assert f.body.get_type() == body.get_type()
        self._f = f
        self._body = body
        self._formal_fv = formal_fv

    @property
    def funct(self) -> K.LocalId:
        return self._f.funct

    @property
    def body(self) -> 'Exp':
        return self._body

    @property
    def formal_fv(self) -> Tup[Tup[K.LocalId, ty.Ty], ...]:
        return self._formal_fv

    @property
    def formal_args(self) -> Tup[K.LocalId, ...]:
        return self._f.formal_args

    def get_type(self) -> ty.TyFun:
        return self._f.get_type()

    def get_arg_type(self, i: int) -> ty.Ty:
        return self._f.get_arg_type(i)

    def get_arg_name(self, i: int) -> K.LocalId:
        return self._f.get_arg_name(i)

    def get_n_args(self) -> int:
        return len(self._f.formal_args)

    def iter_args(self):
        return self._f.iter_args()

    @property
    def bounds(self) -> Tup[int, int]:
        return self._f.bounds

    def __repr__(self):
        return self._f.__repr__()


U = TypeVar("U", bound=ty.Ty)
V = TypeVar("V", bound=K.KNormal)


class Exp:
    __slots__ = ["_kn", "_typ"]

    def __init__(self, node: V):
        assert isinstance(node, K.KNormal)
        # assert not isinstance(node, K.LetRec)
        self._kn: V = node
        self._typ: U = node.get_type()

    def get_type(self) -> U:
        return self._typ

    @property
    def bounds(self) -> Tup[int, int]:
        return self._kn.bounds

    def __str__(self):
        return str(self._kn)


def wrap(cls: Type[K.KNormal], name: str) -> Type[Exp]:
    class Wrapper(Exp):
        __slots__ = []

        def __init__(self, kn: cls):
            assert isinstance(kn, cls)
            super().__init__(kn)

        def get_type(self):
            return self._kn.get_type()

    Wrapper.__name__ = name
    Wrapper.__qualname__ = name

    for k, v in cls.__dict__.items():
        if isinstance(v, property):
            assert v.fset is None
            assert v.fdel is None
            assert v.fget is not None
            f = v.fget
            exec(f"""
@property
def {k}(self):
    return self._kn.{k}
function = {k}
            """)

            p = eval("function")
            setattr(Wrapper, k, p)
            ...

    return Wrapper


Lit = wrap(K.Lit, "Lit")
Var = wrap(K.Var, "Var")
Ext = wrap(K.Ext, "Ext")
# ExtArray = wrap(K.ExtArray, "ExtArray")
# ExtFun = wrap(K.ExtFun, "ExtFun")
Get = wrap(K.Get, "Get")
Unary = wrap(K.Unary, "Unary")
AppCls = wrap(K.App, "AppCls")
AppDir = wrap(K.App, "AppDir")
Binary = wrap(K.Binary, "Binary")

Tuple = wrap(K.Tuple, "Tuple")
Put = wrap(K.Put, "Put")


class Seq(Exp):
    __slots__ = ["_es"]

    def __init__(self, *es: Exp):
        assert all(isinstance(x, Exp) for x in es)
        assert len(es) >= 2
        assert all(x.get_type() is ty.TyUnit() for x in es[:-1])
        super().__init__(es[-1]._kn)
        self._es = es

    @property
    def es(self):
        return self._es


class If(Exp):
    __slots__ = ["_br_true", "_br_false"]

    def __init__(self, kn: K.If, br_true: Exp, br_false: Exp):
        assert isinstance(kn, K.If) and isinstance(br_true, Exp) and isinstance(br_false, Exp)
        assert br_true.get_type() == br_false.get_type() == kn.get_type()
        super().__init__(kn)
        self._br_true = br_true
        self._br_false = br_false

    @property
    def cond(self):
        return self._kn.cond

    @property
    def br_true(self):
        return self._br_true

    @property
    def br_false(self):
        return self._br_false


class Let(Exp):
    __slots__ = ["_rhs", "_expr"]

    def __init__(self, kn: K.Let, rhs: Exp, expr: Exp):
        assert isinstance(kn, K.Let) and isinstance(rhs, Exp) and isinstance(expr, Exp)
        assert rhs.get_type() == kn.rhs.get_type()
        assert expr.get_type() == kn.expr.get_type()
        super().__init__(kn)
        self._rhs = rhs
        self._expr = expr

    @property
    def lhs(self):
        return self._kn.lhs

    @property
    def rhs(self):
        return self._rhs

    @property
    def expr(self):
        return self._expr


class LetTuple(Exp):
    __slots__ = ["_e2"]

    def __init__(self, kn: K.LetTuple, e2: Exp):
        assert isinstance(kn, K.LetTuple) and isinstance(e2, Exp)
        assert e2.get_type() == kn.e2.get_type()
        super().__init__(kn)
        self._e2 = e2

    @property
    def xs(self):
        return self._kn.xs

    @property
    def e1(self):
        return self._kn.e1

    @property
    def e2(self):
        return self._e2


class MakeCls(Exp):
    __slots__ = ["_closure", "_body"]

    def __init__(self, letrec: K.LetRec, closure: Cls, body: Exp):
        assert isinstance(letrec, K.LetRec) and isinstance(closure, Cls) and isinstance(body, Exp)
        super(MakeCls, self).__init__(letrec)
        self._closure = closure
        self._body = body

    @property
    def closure(self) -> Cls:
        return self._closure

    @property
    def body(self):
        return self._body


class ClosureConverter(K.KNormalVisitor):
    def __init__(self, known: Dict[ty.TyFun, Set[K.GlobalId]]):
        self.env: ChainMap[K.Id, ty.Ty] = ChainMap()
        self.known: Set[K.GlobalId | K.LocalId] = {x for v in known.values() for x in v}
        self.toplevel: List[Function] = []

    def convert(self, e: K.KNormal) -> Tup[List[Function], Exp]:
        """
        Converts a KNormal expression into a list of functions and an expression.
        This method modifies e in-place.
        """
        e1 = self.visit(e)
        return self.toplevel.copy(), e1

    def visit(self, e: K.KNormal) -> Exp:
        res = super().visit(e)
        assert isinstance(res, Exp)
        assert res.get_type() == e.get_type()
        return res

    def visit_Lit(self, node: K.Lit) -> Lit:
        return Lit(node)

    def visit_Var(self, node: K.Var) -> Var:
        return Var(node)

    def visit_Ext(self, node: K.Ext) -> Ext:
        if isinstance(node.get_type(), ty.TyFun):
            self.known.add(node.name)
        return Ext(node)

    # def visit_ExtFun(self, node: K.ExtFun) -> ExtFun:
    #     self.known.add(node.name)
    #     return ExtFun(node)

    def visit_Get(self, node: K.Get) -> Get:
        return Get(node)

    def visit_Unary(self, node: K.Unary) -> Unary:
        return Unary(node)

    def visit_App(self, node: K.App) -> AppCls | AppDir:
        callee = node.callee
        if callee in self.known:
            assert isinstance(callee, (K.GlobalId, K.LocalId))
            logger.info(f"directly applying closure '{callee!r}'")
            return AppDir(node)
        else:
            return AppCls(node)

    def visit_AppDir(self, node: K.App) -> AppDir:
        """
        This method can be called because in visit_LetRec, there may be need to visit function's body one more time.
        """
        assert isinstance(node, AppDir)
        return node

    def visit_AppCls(self, node: K.App) -> AppCls:
        """This method can be called, due to the same reason as visit_AppDir."""
        assert isinstance(node, AppCls)
        return node

    def visit_Binary(self, node: K.Binary) -> Binary:
        return Binary(node)

    def visit_Seq(self, node: K.Seq) -> Seq:
        xs = [self.visit(x) for x in node.es]
        assert all(x.get_type() is e.get_type() for x, e in zip(xs, node.es))
        return Seq(*xs)

    def visit_Tuple(self, node: K.Tuple) -> Tuple:
        return Tuple(node)

    def visit_Put(self, node: K.Put) -> Put:
        return Put(node)

    def visit_If(self, node: K.If) -> If:
        return If(node, self.visit(node.br_true), self.visit(node.br_false))

    def visit_Let(self, node: K.Let) -> Let:
        rhs = self.visit(node.rhs)
        self.env = self.env.new_child({node.lhs: rhs.get_type()})
        expr = self.visit(node.expr)
        self.env = self.env.parents
        return Let(node, rhs, expr)

    def visit_LetTuple(self, node: K.LetTuple) -> LetTuple:
        assert node.e1 in self.env
        e1_ty = self.env[node.e1]
        assert isinstance(e1_ty, ty.TyTuple) and len(e1_ty.elems) == len(node.xs)
        self.env = self.env.new_child(m={x: t for x, t in zip(node.xs, e1_ty.elems)})
        e2 = self.visit(node.e2)
        self.env = self.env.parents
        return LetTuple(node, e2)

    def visit_LetRec(self, node: K.LetRec) -> Exp:
        toplevel_backup = self.toplevel.copy()
        self.env.new_child({node.f.funct: node.get_type()})
        self.env.update({arg: argty for arg, argty in node.f.iter_args()})
        self.known.add(node.f.funct)
        body1 = self.visit(node.f.body)

        def fv(x: Exp):
            fv_visitor = Fv()
            fv_visitor.visit(x)
            return fv_visitor.fv

        zs = fv(body1).difference(node.f.formal_args)

        if len(zs) > 0:
            def quoted(x: str):
                return f"'{x}'"

            logger.info(
                f"free variable(s) found in function '{node.f.funct!r}': {', '.join(str(z) for z in zs)}")
            logger.info(f"function {node.f.funct!r} cannot be directly applied in fact")

            self.toplevel = toplevel_backup
            self.known.remove(node.f.funct)
            body1 = self.visit(node.f.body)

        zs = list(fv(body1).difference({node.f.funct}.union(node.f.formal_args)))
        zts = [(z, self.env[z]) for z in zs]

        # body1 has to be a subclass of Exp. if not, the following line will raise an error
        func = Function(node.f, body1, tuple(zts))
        self.toplevel.append(func)
        self.env = self.env.parents
        self.env = self.env.new_child({node.f.funct: func.get_type()})
        e2 = self.visit(node.e)
        self.env = self.env.parents
        if node.f.funct in fv(e2):
            return MakeCls(node, Cls(func, tuple(zs)), e2)
        else:
            logger.info(f"eliminating closure {node.f.funct!r}")
            return e2


T = TypeVar("T")


class ExpVisitor(ABC, Generic[T]):
    __slots__ = []

    @abstractmethod
    def visit_Lit(self, node: Lit) -> T:
        ...

    @abstractmethod
    def visit_Var(self, node: Var) -> T:
        ...

    @abstractmethod
    def visit_Ext(self, node: Ext) -> T:
        ...

    # @abstractmethod
    # def visit_ExtFun(self, node: ExtFun) -> T:
    #     ...

    @abstractmethod
    def visit_Get(self, node: Get) -> T:
        ...

    @abstractmethod
    def visit_Unary(self, node: Unary) -> T:
        ...

    @abstractmethod
    def visit_AppCls(self, node: AppCls) -> T:
        ...

    @abstractmethod
    def visit_AppDir(self, node: AppDir) -> T:
        ...

    @abstractmethod
    def visit_Binary(self, node: Binary) -> T:
        ...

    @abstractmethod
    def visit_Seq(self, node: Seq) -> T:
        ...

    @abstractmethod
    def visit_Tuple(self, node: Tuple) -> T:
        ...

    @abstractmethod
    def visit_Put(self, node: Put) -> T:
        ...

    @abstractmethod
    def visit_If(self, node: If) -> T:
        ...

    @abstractmethod
    def visit_Let(self, node: Let) -> T:
        ...

    @abstractmethod
    def visit_LetTuple(self, node: LetTuple) -> T:
        ...

    @abstractmethod
    def visit_MakeCls(self, node: MakeCls) -> T:
        ...

    def visit(self, node: Exp) -> T:
        return getattr(self, f"visit_{node.__class__.__name__}")(node)


del T


class Fv(ExpVisitor[None]):

    def __init__(self):
        self.__fv: Set[K.LocalId] = set()

    @property
    def fv(self) -> FrozenSet[K.LocalId]:
        assert all(isinstance(x, K.LocalId) for x in self.__fv)
        return frozenset(self.__fv)

    def __do_nothing(self, node: Exp) -> None:
        pass

    @staticmethod
    def __gen_fv_fn(acc_fvs: Tup[str, ...] = (), iter_acc_fvs: Tup[str, ...] = (), visits: Tup[str, ...] = ()) -> \
            Callable[
                [Self, Exp], None]:
        def f(self: Self, node: Exp) -> None:
            for x in acc_fvs:
                y = getattr(node, x)
                assert isinstance(y, K.Id)
                y.acc_fv(self.__fv)

            for x in iter_acc_fvs:
                y = getattr(node, x)
                assert isinstance(y, Iterable)
                for z in y:
                    assert isinstance(z, K.Id)
                    z.acc_fv(self.__fv)

            for x in visits:
                y = getattr(node, x)
                assert isinstance(y, Exp)
                self.visit(y)

        return f

    visit_Lit = __do_nothing

    def visit_Var(self, node: Var) -> None:
        self.__fv.add(node.name)

    visit_Ext = __do_nothing
    # visit_ExtArray = __do_nothing
    # visit_ExtFun = __do_nothing

    visit_Get = __gen_fv_fn(('array', 'index'))

    visit_Unary = __gen_fv_fn(('e',))

    visit_AppCls = __gen_fv_fn(('callee',), ('args',))

    def visit_AppDir(self, node: AppDir):
        for x in node.args:
            x.acc_fv(self.__fv)

    visit_Binary = __gen_fv_fn(('e1', 'e2'))

    def visit_Seq(self, node: Seq) -> None:
        for e in node.es:
            self.visit(e)

    visit_Tuple = __gen_fv_fn((), iter_acc_fvs=('elems',))

    visit_Put = __gen_fv_fn(('array', 'index', 'value'))

    visit_If = __gen_fv_fn(('cond',), visits=('br_true', 'br_false'))

    def visit_Let(self, node: Let) -> None:
        self.visit(node.expr)
        node.lhs.rm_fv(self.__fv)
        self.visit(node.rhs)

    def visit_LetTuple(self, node: LetTuple) -> None:
        self.visit(node.e2)
        for x in node.xs:
            self.__fv.discard(x)
        node.e1.acc_fv(self.__fv)

    def visit_MakeCls(self, node: MakeCls) -> None:
        self.visit(node.body)
        self.__fv |= node.closure.actual_fv
        self.__fv.discard(node.closure.entry.funct)
