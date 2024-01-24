import contextlib
import logging
from collections import ChainMap
from .language import Expr, Lit, Var, Get, Unary, App, Binary, Semi, Tuple, Put, If, Let, LetRec, LetTuple, Decl, \
    DeclRec, \
    TopLevel, Function
from ty0 import TyCon, TyVar, Ty0, is_ty0
from ty0 import ty0_int, ty0_float, ty0_bool, ty0_unit, ty0_fun, ty0_array, ty0_tuple
from withbounds import WithBounds
from bounds import Bounds
from .. import bind_logger

get_adapter = bind_logger(logger=logging.getLogger(__name__))


class InferError(Exception):
    def __init__(self, bounds: Bounds | None):
        super().__init__()
        self._bounds = bounds

    @property
    def bounds(self) -> Bounds | None:
        return self._bounds

    @bounds.setter
    def bounds(self, bounds: Bounds):
        assert self._bounds is None and isinstance(bounds, Bounds)
        self._bounds = bounds


class UnifyError(InferError):
    def __init__(self, t1: Ty0, t2: Ty0, bounds: Bounds):
        super().__init__(bounds)
        self.t1 = t1
        self.t2 = t2
        with get_adapter(bounds=bounds) as adapter:
            adapter.error(f"cannot unify '{t1}' and '{t2}'")


class RecursiveType(InferError):
    def __init__(self, t: TyVar, ty: Ty0, bounds: Bounds | None = None):
        super().__init__(bounds)
        self.t = t
        self.ty = ty
        with get_adapter(bounds=bounds) as adapter:
            adapter.error(f"{t} occurs in {ty}")


class UnionFind:
    def __init__(self):
        self._parent: dict[Ty0, Ty0] = {}
        self._rank: dict[Ty0, int] = {}
        self._rp: dict[Ty0, TyCon] = {}

    def find(self, t: Ty0, /) -> Ty0:
        if t not in self._parent:
            self._parent[t] = t
            self._rank[t] = 0
            if isinstance(t, TyCon):
                self._rp[t] = t
            return t
        if self._parent[t] == t:
            return t
        self._parent[t] = f = self.find(self._parent[t])
        return f

    def merge(self, t1: Ty0, t2: Ty0, bounds: Bounds):
        t1 = self.find(t1)
        t2 = self.find(t2)
        assert self._parent[t1] == t1
        assert self._parent[t2] == t2
        if t1 == t2:
            return
        rp1, rp2 = self._rp.get(t1), self._rp.get(t2)
        if rp1 is not None and rp2 is not None:
            if rp1 != rp2:
                raise UnifyError(rp1, rp2, bounds)
        if rp1 is not None:
            self._rp[t2] = rp1
        elif rp2 is not None:
            self._rp[t1] = rp2

        if self._rank[t1] < self._rank[t2]:
            t1, t2 = t2, t1
        # now rank[t1] >= rank[t2]
        if self._rank[t1] == self._rank[t2]:
            self._rank[t1] += 1
        del self._rank[t2]
        self._parent[t2] = t1

    def rp(self, t: Ty0, /) -> TyCon | None:
        return self._rp.get(self.find(t))

    def apply(self, t: Ty0, b: Bounds | None = None, /) -> Ty0:
        if isinstance(t, TyCon):
            return TyCon(t.name, *[self.apply(a, b) for a in t.args])
        else:
            f = self.find(t)
            if (rp := self.rp(f)) is not None:
                if self.occurs_in(t, rp):
                    raise RecursiveType(t, rp, b)
                else:
                    return self.apply(rp, b)
            else:
                return f

    def occurs_in(self, t1: TyVar, t2: Ty0) -> bool:
        assert isinstance(t1, TyVar) and is_ty0(t2)
        if t1 == t2:
            return True
        match t2:
            case TyCon(_, args):
                return any(self.occurs_in(t1, a) for a in args)
            case TyVar():
                if (t := self.rp(t2)) is None:
                    return False
                else:
                    return self.occurs_in(t1, t)

    def __str__(self):
        families: dict[Ty0, list[Ty0]] = {}
        for t in self._parent:
            f = self.find(t)
            families.setdefault(f, []).append(t)
        for v in families.values():
            v.sort(key=lambda t: -100 if isinstance(t, TyCon) else 0)
        return "\n".join(
            f"{f}: {', '.join(str(t) for t in families[f])}" for f in families
        )

    def check(self):
        families: dict[Ty0, list[Ty0]] = {}
        for t in self._parent:
            f = self.find(t)
            families.setdefault(f, []).append(t)
        for v in families.values():
            assert len(v) >= 1
            rp = self.rp(v[0])
            assert rp is None or isinstance(rp, TyCon)
            for i in range(1, len(v)):
                if isinstance(v[i], TyCon):
                    assert v[i] is rp
                assert self.rp(v[i]) is rp


class Ty0Scheme:
    __slots__ = ["_polys", "_ty0"]

    def __init__(self, polys: frozenset[TyVar], qt: Ty0):
        assert is_ty0(qt)
        self._polys = polys
        self._ty0 = qt
        assert qt.tv.issuperset(polys)

    def __str__(self):
        return f"{' '.join(str(v) for v in self._polys)}. {self._ty0}"

    @staticmethod
    def from_ty0(ty: Ty0) -> 'Ty0Scheme':
        return Ty0Scheme(frozenset(), ty)

    @staticmethod
    def quantify(vs: set[TyVar], qt: Ty0) -> 'Ty0Scheme':
        return Ty0Scheme(qt.tv.intersection(vs), qt)

    def apply_with(self, uf: UnionFind):
        ty0 = uf.apply(self._ty0)
        return Ty0Scheme(ty0.tv.intersection(self._polys), ty0)

    def monomorphize_with(self, mono: 'Monomorphization'):
        return mono.visit(self._ty0)[0]

    def specialize_with(self, *args: Ty0) -> Ty0:
        assert len(args) == len(self._polys)
        subst = {v: a for v, a in zip(self._polys, args)}

        def subst_ty(t: Ty0) -> Ty0:
            match t:
                case TyCon(con, args):
                    if self._polys.isdisjoint(t.tv):
                        return t
                    return TyCon(con, *[subst_ty(a) for a in args])
                case TyVar():
                    return subst.get(t, t)

        return subst_ty(self._ty0)

    def instantiate(self) -> Ty0:
        subst = {v: TyVar() for v in self._polys}

        def subst_ty(t: Ty0) -> Ty0:
            match t:
                case TyCon(con, args):
                    if self._polys.isdisjoint(t.tv):
                        return t
                    return TyCon(con, *[subst_ty(a) for a in args])
                case TyVar():
                    return subst.get(t, t)

        return subst_ty(self._ty0)

    __repr__ = __str__


class TypingExpr:
    def __init__(self):
        self.env = ChainMap[str, Ty0]()
        a = TyVar()
        array_make_sc = Ty0Scheme(frozenset([a]), ty0_fun(ty0_int, a, ty0_array(a)))
        self.ext: dict[str, Ty0Scheme] = {"Array.make": array_make_sc, "Array.create": array_make_sc}
        del a, array_make_sc

        self.predicates: set[tuple[str, Ty0, Bounds]] = set()
        self.funcs: dict[WithBounds[str], Ty0] = {}
        self.uf = UnionFind()

    @contextlib.contextmanager
    def _new_child_env(self, env: dict[str, Ty0]):
        self.env = self.env.new_child(env)
        try:
            yield
        finally:
            self.env = self.env.parents

    def unify(self, t1: Ty0, t2: Ty0, bounds: Bounds):
        t1, t2 = self.uf.find(t1), self.uf.find(t2)
        t1, t2 = self.uf.rp(t1) or t1, self.uf.rp(t2) or t2
        match t1, t2:
            case TyCon(name1, args1), TyCon(name2, args2):
                if name1 != name2:
                    raise UnifyError(t1, t2, bounds)
                if len(args1) != len(args2):
                    raise UnifyError(t1, t2, bounds)
                for a1, a2 in zip(args1, args2):
                    self.unify(a1, a2, bounds)
            case (TyVar(), _) | (_, TyVar()):
                self.uf.merge(t1, t2, bounds)
            case _:
                raise UnifyError(t1, t2, bounds)

    def visit(self, node: Expr):
        t = getattr(self, f"visit_{node.__class__.__name__}")(node)
        assert is_ty0(t)
        return t

    def visit_Lit(self, node: Lit) -> Ty0:
        match node.lit.val:
            # bool is a subclass of int, so we need to check bool first.
            case bool():
                return ty0_bool
            case int():
                return ty0_int
            case float():
                return ty0_float
            case '()':
                return ty0_unit

    def visit_Var(self, node: Var) -> Ty0:
        try:
            node.ty0.set_result(v := self.env[node.name.val])
            # node.is_ext.set_result(False)
            return v
        except KeyError:
            # node.is_ext.set_result(True)
            try:
                node.ty0.set_result(v := self.ext[node.name.val].instantiate())
                return v
            except KeyError:
                with get_adapter(bounds=node.bounds) as adapter:
                    adapter.info(f"variable '{node}' assumed as external")
                node.ty0.set_result(v := TyVar())
                self.ext[node.name.val] = Ty0Scheme.from_ty0(v)
                return v

    def visit_Get(self, node: Get) -> Ty0:
        t1 = self.visit(node.e1)
        a = TyVar()
        self.unify(t1, ty0_array(a), node.e1.bounds)
        t2 = self.visit(node.e2)
        self.unify(t2, ty0_int, node.e2.bounds)
        return a

    def visit_Unary(self, node: Unary) -> Ty0:
        t = self.visit(node.e)
        match node.op.val:
            case '-':
                self.predicates.add(('Num', t, node.e.bounds))
                return t
            case '-.':
                self.unify(t, ty0_float, node.e.bounds)
                return ty0_float
            
    def visit_App(self, node: App) -> Ty0:
        ty_callee = self.visit(node.callee)
        ty_ret = TyVar()
        ty_args = [self.visit(e) for e in node.args]
        self.unify(ty_callee, ty0_fun(*ty_args, ty_ret), node.callee.bounds)
        return ty_ret

    def visit_Binary(self, node: Binary) -> Ty0:
        t1 = self.visit(node.e1)
        t2 = self.visit(node.e2)
        match node.op.val:
            case '+' | '-' | '*' | '/':
                self.predicates.add(('Num', t1, node.e1.bounds))
                self.predicates.add(('Num', t2, node.e2.bounds))
                self.unify(t1, t2, node.bounds)
                return t1
            case '+.' | '-.' | '*.' | '/.':
                self.unify(t1, ty0_float, node.e1.bounds)
                self.unify(t2, ty0_float, node.e2.bounds)
                return ty0_float
            case '=' | '<>':
                self.predicates.add(('Eq', t1, node.e1.bounds))
                self.predicates.add(('Eq', t2, node.e2.bounds))
                self.unify(t1, t2, node.op.bounds)
                return ty0_bool
            case '<' | '>' | '<=' | '>=':
                self.predicates.add(('Ord', t1, node.e1.bounds))
                self.predicates.add(('Ord', t2, node.e2.bounds))
                self.unify(t1, t2, node.op.bounds)
                return ty0_bool

    def visit_Semi(self, node: Semi) -> Ty0:
        for e in node.es[:-1]:
            self.unify(self.visit(e), ty0_unit, e.bounds)
        return self.visit(node.es[-1])

    def visit_Tuple(self, node: Tuple) -> TyCon:
        return ty0_tuple(*[self.visit(e) for e in node.es])

    def visit_Put(self, node: Put) -> TyCon:
        t2 = self.visit(node.e2)
        self.unify(t2, ty0_int, node.e2.bounds)
        t1 = self.visit(node.e1)
        t3 = self.visit(node.e3)
        self.unify(t1, ty0_array(t3), node.e1.bounds)
        return ty0_unit

    def visit_If(self, node: If) -> Ty0:
        t1 = self.visit(node.e1)
        self.unify(t1, ty0_bool, node.e1.bounds)
        t2 = self.visit(node.e2)
        t3 = self.visit(node.e3)
        self.unify(t2, t3, node.e2.bounds)
        return t2

    def visit_Let(self, node: Let) -> Ty0:
        t1 = self.visit(node.binding.e1)
        with self._new_child_env({node.binding.var.val: t1}):
            return self.visit(node.e2)

    def visit_Function(self, f: Function) -> Ty0:
        ty_args, ty_ret = [TyVar() for _ in f.formal_args], TyVar()
        ty_func = ty0_fun(*ty_args, ty_ret)
        assert f.funct not in self.funcs
        self.funcs[f.funct] = ty_func
        with self._new_child_env({f.funct.val: ty_func}):
            # if there is an argument that has the same name as the function, then the function itself is shadowed.
            self.env.update({x.val: t for x, t in zip(f.formal_args, ty_args)})
            ty_body = self.visit(f.e1)
        self.unify(ty_ret, ty_body, f.e1.bounds)
        return ty_func

    def visit_LetRec(self, node: LetRec) -> Ty0:
        f, e2 = node.f, node.e2
        assert f.funct not in self.funcs
        self.funcs[f.funct] = ty_func = self.visit_Function(f)
        with self._new_child_env({f.funct.val: ty_func}):
            return self.visit(e2)

    def visit_LetTuple(self, node: LetTuple):
        t1 = self.visit(node.e1)
        ts = [TyVar() for _ in node.xs]
        self.unify(t1, ty0_tuple(*ts), node.e1.bounds)
        with self._new_child_env({x.val: t for x, t in zip(node.xs, ts)}):
            return self.visit(node.e2)


class Typing:
    def __init__(self):
        self.expr_visitor = TypingExpr()
        self.uf: UnionFind = self.expr_visitor.uf

    @property
    def funcs(self):
        return self.expr_visitor.funcs

    def infer(self, node: TopLevel) -> list[WithBounds[Ty0]]:
        ts = self.visit_TopLevel(node)
        ev = self.expr_visitor
        ev.uf.check()
        for i in range(len(ts)):
            ts[i].val = ev.uf.apply(ts[i].val)
        predicates: set[tuple[str, Ty0, Bounds]] = set()
        for name, ty, bounds in ev.predicates:
            ty = ev.uf.apply(ty)
            match name, ty:
                case 'Num', TyCon('int' | 'float', _):
                    ...
                case 'Eq', TyCon('int' | 'float' | 'bool', _):
                    ...
                case 'Ord', TyCon('int' | 'float', _):
                    ...
                case ('Num' | 'Eq' | 'Ord'), TyVar():
                    ...
                case _:
                    with get_adapter(bounds=bounds) as adapter:
                        adapter.error(f"cannot find an instance of {name} '{ty}'")
                    raise TypeError(f"cannot find an instance of {name} '{ty}'")
            predicates.add((name, ty, bounds))
        ev.predicates = predicates

        for k in ev.ext:
            v = ev.ext[k]
            ev.ext[k] = v.apply_with(ev.uf)

        for f in ev.funcs:
            ev.funcs[f] = ev.uf.apply(ev.funcs[f])

        return ts

    def visit_Decl(self, node: Decl) -> None:
        ev = self.expr_visitor
        assert len(ev.env.maps) == 1
        ev.env[node.binding.var.val] = ev.visit(node.binding.e1)

    def visit_DeclRec(self, node: DeclRec) -> None:
        ev = self.expr_visitor
        assert len(ev.env.maps) == 1
        ev.funcs[node.f.funct] = ev.env[node.f.funct.val] = ev.visit_Function(node.f)

    def visit_TopLevel(self, node: TopLevel):
        ts: list[WithBounds[Ty0]] = []
        for decl_or_expr in node.decl_or_exprs:
            if isinstance(decl_or_expr, Decl):
                self.visit_Decl(decl_or_expr)
            elif isinstance(decl_or_expr, DeclRec):
                self.visit_DeclRec(decl_or_expr)
            else:
                t = self.expr_visitor.visit(decl_or_expr)
                self.expr_visitor.unify(t, ty0_unit, decl_or_expr.bounds)
                ts.append(WithBounds(t, decl_or_expr.bounds))
        return ts


class Monomorphization:
    __slots__ = 'uf',
    from ty import Ty, TyInt, TyFloat, TyBool, TyUnit, TyFun, TyTuple, TyArray

    def __init__(self, uf: UnionFind):
        self.uf = uf

    def visit(self, ty: Ty0, b: Bounds | None = None, /):
        match ty:
            case TyCon():
                return self.visit_tycon(ty, b)
            case TyVar():
                match self.uf.apply(ty, b):
                    case TyCon() as tycon:
                        return self.visit_tycon(tycon, b)
                    case TyVar():
                        return Monomorphization.TyInt(), {ty}

    def visit_tycon(self, ty: TyCon, b: Bounds | None = None, /) -> tuple[Ty, set[TyVar]]:
        match ty.name, ty.args:
            case 'int', []:
                return Monomorphization.TyInt(), set()
            case 'float', []:
                return Monomorphization.TyFloat(), set()
            case 'bool', []:
                return Monomorphization.TyBool(), set()
            case 'unit', []:
                return Monomorphization.TyUnit(), set()
            case '->', [_, _, *_]:
                us: set[TyVar] = set()
                args: list[Monomorphization.Ty] = []
                for a in ty.args:
                    a, u = self.visit(a, b)
                    args.append(a)
                    us |= u
                return self.TyFun(*args), us
            case 'tuple', [_, _, *_]:
                us = set()
                args = []
                for a in ty.args:
                    a, u = self.visit(a, b)
                    args.append(a)
                    us |= u
                return self.TyTuple(args), us
            case 'array', [_]:
                a, u = self.visit(ty.args[0], b)
                return self.TyArray(a), u
            case _:
                raise NotImplementedError(ty)
