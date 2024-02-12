import logging
from .language import Expr, LitU, LitB, LitI, LitF, Var, Get, Unary, App, Binary, Semi, Tuple, Put, If, Let, LetRec, \
    LetTuple, Decl, \
    DeclRec, \
    TopLevel, Function
from ty0 import TyCon, TyVar, Ty0, is_ty0
from ty0 import ty0_int, ty0_float, ty0_bool, ty0_unit, ty0_fun, ty0_array, ty0_tuple
from metadata import DILocation, DIVariable
from id import Id
from .. import bind_logger

get_adapter = bind_logger(logger=logging.getLogger(__name__))


class InferError(Exception):
    ...


class UnifyError(InferError):
    def __init__(self, t1: Ty0, t2: Ty0):
        self.t1 = t1
        self.t2 = t2
        self.reraised = False

    def dump(self):
        return f"cannot unify '{self.t1}' and '{self.t2}'"


class RecursiveType(InferError):
    def __init__(self, t: TyVar, ty: Ty0):
        self.t = t
        self.ty = ty
        self.reraised = False

    def dump(self):
        return f"{self.t} occurs in {self.ty}"


class NoInstance(InferError):
    def __init__(self, name: str, ty: Ty0):
        self.name = name
        self.ty = ty
        self.reraised = False

    def dump(self):
        return f"cannot find an instance of {self.name} '{self.ty}'"


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

    def merge(self, t1: Ty0, t2: Ty0, /):
        t1 = self.find(t1)
        t2 = self.find(t2)
        assert self._parent[t1] == t1 and self._parent[t2] == t2
        if t1 == t2:
            return
        rp1, rp2 = self._rp.get(t1), self._rp.get(t2)
        if rp1 is not None and rp2 is not None:
            if rp1 != rp2:
                raise UnifyError(rp1, rp2)
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

    def apply(self, t: Ty0, /) -> Ty0:
        """
        :raise RecursiveType: if t occurs in its representative
        """
        if isinstance(t, TyCon):
            return TyCon(t.name, *[self.apply(a) for a in t.args])
        else:
            f = self.find(t)
            if (rp := self.rp(f)) is not None:
                if self.occurs_in(t, rp):
                    raise RecursiveType(t, rp)
                else:
                    return self.apply(rp)
            else:
                return f

    def occurs_in(self, t1: TyVar, t2: Ty0, /) -> bool:
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
        from collections import defaultdict
        families = defaultdict[Ty0, list[Ty0]]()
        for t in self._parent:
            f = self.find(t)
            families[f].append(t)
        
        for v in families.values():
            v.sort(key=lambda t: -100 if isinstance(t, TyCon) else 0)
        return "\n".join(
            f"{f}: {', '.join(map(str, families[f]))}" for f in families
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


# class Ty0Scheme:
#     __slots__ = ["_polys", "_ty0"]

#     def __init__(self, polys: frozenset[TyVar], qt: Ty0):
#         assert is_ty0(qt)
#         self._polys = polys
#         self._ty0 = qt
#         assert qt.tv.issuperset(polys)

#     def __str__(self):
#         return f"{' '.join(str(v) for v in self._polys)}. {self._ty0}"

#     @staticmethod
#     def from_ty0(ty: Ty0) -> 'Ty0Scheme':
#         return Ty0Scheme(frozenset(), ty)

#     @staticmethod
#     def quantify(vs: set[TyVar], qt: Ty0) -> 'Ty0Scheme':
#         return Ty0Scheme(qt.tv.intersection(vs), qt)

#     def apply_with(self, uf: UnionFind):
#         ty0 = uf.apply(self._ty0)
#         return Ty0Scheme(ty0.tv.intersection(self._polys), ty0)

#     def monomorphize_with(self, mono: 'Monomorphization'):
#         return mono.visit(self._ty0)[0]

#     def specialize_with(self, *args: Ty0) -> Ty0:
#         assert len(args) == len(self._polys)
#         subst = {v: a for v, a in zip(self._polys, args)}

#         def subst_ty(t: Ty0) -> Ty0:
#             match t:
#                 case TyCon(con, args):
#                     if self._polys.isdisjoint(t.tv):
#                         return t
#                     return TyCon(con, *[subst_ty(a) for a in args])
#                 case TyVar():
#                     return subst.get(t, t)

#         return subst_ty(self._ty0)

#     def instantiate(self) -> Ty0:
#         subst = {v: TyVar() for v in self._polys}

#         def subst_ty(t: Ty0) -> Ty0:
#             match t:
#                 case TyCon(con, args):
#                     if self._polys.isdisjoint(t.tv):
#                         return t
#                     return TyCon(con, *[subst_ty(a) for a in args])
#                 case TyVar():
#                     return subst.get(t, t)

#         return subst_ty(self._ty0)

#     __repr__ = __str__


class TypingExpr:
    def __init__(self, env: dict[Id, Ty0]):
        self.env = env
        # a = TyVar()
        # array_make_sc = Ty0Scheme(frozenset([a]), ty0_fun(ty0_int, a, ty0_array(a)))
        # self.ext: dict[str, Ty0Scheme] = {"Array.make": array_make_sc, "Array.create": array_make_sc}
        # del a, array_make_sc

        self.predicates: set[tuple[str, Ty0, DILocation]] = set()
        self.funcs: dict[Id, Ty0] = {}
        self.di_vars: dict[Id, DIVariable] = {}
        self.array_makes: dict[Id, Ty0] = {}
        self.uf = UnionFind()

    # @contextlib.contextmanager
    # def _new_child_env(self, env: dict[str, Ty0]):
    #     self.env = self.env.new_child(env)
    #     try:
    #         yield
    #     finally:
    #         self.env = self.env.parents

    def unify(self, t1: Ty0, t2: Ty0, /):
        t1, t2 = self.uf.find(t1), self.uf.find(t2)
        t1, t2 = self.uf.rp(t1) or t1, self.uf.rp(t2) or t2
        match t1, t2:
            case TyCon(name1, args1), TyCon(name2, args2):
                if name1 != name2:
                    raise UnifyError(t1, t2)
                if len(args1) != len(args2):
                    raise UnifyError(t1, t2)
                for a1, a2 in zip(args1, args2):
                    self.unify(a1, a2)
            case (TyVar(), _) | (_, TyVar()):
                self.uf.merge(t1, t2)
            case _:
                raise UnifyError(t1, t2)

    def visit(self, node: Expr, /, expected: Ty0 | None = None) -> Ty0:
        try:
            match node:
                case LitU():
                    res = ty0_unit
                case LitB():
                    res = ty0_bool
                case LitI():
                    res = ty0_int
                case LitF():
                    res = ty0_float
                case Var():
                    if node.metadata.name == 'Array.make':
                        a = TyVar()
                        res = ty0_fun(ty0_int, a, ty0_array(a))
                        self.array_makes[node.name] = res
                        self.di_vars[node.name] = node.metadata
                        node.ty0.set_result(res)
                    else:
                        node.ty0.set_result(res := self.env[node.name])
                case Get():
                    res = self.visit_Get(node)
                case Unary():
                    res = self.visit_Unary(node)
                case App():
                    res = self.visit_App(node)
                case Binary():
                    res = self.visit_Binary(node)
                case Semi():
                    res = self.visit_Semi(node)
                case Tuple():
                    res = self.visit_Tuple(node)
                case Put():
                    res = self.visit_Put(node)
                case If():
                    res = self.visit_If(node)
                case Let():
                    res = self.visit_Let(node)
                case LetTuple():
                    res = self.visit_LetTuple(node)
                case LetRec():
                    res = self.visit_LetRec(node)
                case _:
                    raise NotImplementedError(node)
            if expected is not None:
                self.unify(res, expected)

            res = self.uf.apply(res)

        except (UnifyError, RecursiveType) as e:
            if not e.reraised:
                e.reraised = True
                with get_adapter(bounds=node.location.get_bounds()) as adapter:
                    adapter.error(e.dump())
            raise e
        return res

    # def visit_Var(self, node: Var) -> Ty0:
    #     try:
    #         node.ty0.set_result(v := self.env[node.name.val])
    #         # node.is_ext.set_result(False)
    #         return v
    #     except KeyError:
    #         # node.is_ext.set_result(True)
    #         try:
    #             node.ty0.set_result(v := self.ext[node.name.val].instantiate())
    #             return v
    #         except KeyError:
    #             with get_adapter(bounds=node.bounds) as adapter:
    #                 adapter.info(f"variable '{node}' assumed as external")
    #             node.ty0.set_result(v := TyVar())
    #             self.ext[node.name.val] = Ty0Scheme.from_ty0(v)
    #             return v

    def visit_Get(self, node: Get, /) -> Ty0:
        a = TyVar()
        self.visit(node.e1, ty0_array(a))
        self.visit(node.e2, ty0_int)
        return a

    def visit_Unary(self, node: Unary, /) -> Ty0:
        match node.op:
            case '-':
                t = self.visit(node.e)
                self.predicates.add(('Num', t, node.metadata))
                return t
            case '-.':
                return self.visit(node.e, ty0_float)
            case _:
                raise NotImplementedError(node.op)

    def visit_App(self, node: App, /) -> Ty0:
        ty_args = [self.visit(e) for e in node.args]
        ty_ret = TyVar()
        _ = self.visit(node.callee, ty0_fun(*ty_args, ty_ret))
        return ty_ret

    def visit_Binary(self, node: Binary, /) -> Ty0:
        match node.op:
            case '+' | '-' | '*' | '/':
                t1 = self.visit(node.e1)
                _ = self.visit(node.e2, t1)
                self.predicates.add(('Num', t1, node.metadata))
                return t1
            case '+.' | '-.' | '*.' | '/.':
                self.visit(node.e1, ty0_float)
                self.visit(node.e2, ty0_float)
                return ty0_float
            case '=' | '<>':
                t1 = self.visit(node.e1)
                _ = self.visit(node.e2, t1)
                self.predicates.add(('Eq', t1, node.metadata))
                return ty0_bool
            case '<' | '>' | '<=' | '>=':
                t1 = self.visit(node.e1)
                _ = self.visit(node.e2, t1)
                self.predicates.add(('Ord', t1, node.metadata))
                return ty0_bool
            case _:
                raise NotImplementedError(node.op)

    def visit_Semi(self, node: Semi, /) -> Ty0:
        for e in node.es[:-1]:
            self.visit(e, ty0_unit)
        return self.visit(node.es[-1])

    def visit_Tuple(self, node: Tuple, /) -> TyCon:
        return ty0_tuple(*[self.visit(e) for e in node.es])

    def visit_Put(self, node: Put, /) -> TyCon:
        self.visit(node.e2, ty0_int)
        t3 = self.visit(node.e3)
        self.visit(node.e1, ty0_array(t3))
        return ty0_unit

    def visit_If(self, node: If, /) -> Ty0:
        self.visit(node.e1, ty0_bool)
        t2 = self.visit(node.e2)
        self.visit(node.e3, t2)
        return t2

    def visit_Let(self, node: Let, /) -> Ty0:
        t1 = self.visit(node.binding.e1)
        self.env[node.binding.var.name] = t1
        self.di_vars[node.binding.var.name] = node.binding.var.metadata
        # with self._new_child_env({node.binding.var.val: t1}):
        return self.visit(node.e2)

    def visit_Function(self, f: Function, /) -> Ty0:
        ty_args, ty_ret = [TyVar() for _ in f.formal_args], TyVar()
        ty_func = ty0_fun(*ty_args, ty_ret)
        assert f.funct.name not in self.funcs
        self.funcs[f.funct.name] = ty_func
        self.di_vars[f.funct.name] = f.funct.metadata
        self.env[f.funct.name] = ty_func
        # with self._new_child_env({f.funct.val: ty_func}):
        # if there is an argument that has the same name as the function, then the function itself is shadowed.
        self.env.update({x.name: t for x, t in zip(f.formal_args, ty_args)})
        self.di_vars.update({x.name: x.metadata for x in f.formal_args})
        self.visit(f.e1, ty_ret)
        return ty_func

    def visit_LetRec(self, node: LetRec, /) -> Ty0:
        f, e2 = node.f, node.e2
        assert f.funct.name not in self.funcs
        self.funcs[f.funct.name] = ty_func = self.visit_Function(f)
        self.di_vars[f.funct.name] = f.funct.metadata
        self.env[f.funct.name] = ty_func
        # with self._new_child_env({f.funct.val: ty_func}):
        return self.visit(e2)

    def visit_LetTuple(self, node: LetTuple, /):
        ts = [TyVar() for _ in node.xs]
        self.visit(node.e1, ty0_tuple(*ts))
        self.env.update({x.name: t for x, t in zip(node.xs, ts)})
        self.di_vars.update({x.name: x.metadata for x in node.xs})
        # with self._new_child_env({x.val: t for x, t in zip(node.xs, ts)}):
        return self.visit(node.e2)


class Typing:
    def __init__(self, ty_env: dict[Id, Ty0]):
        self.expr_visitor = TypingExpr(ty_env)
        self.uf: UnionFind = self.expr_visitor.uf

    @property
    def funcs(self):
        return self.expr_visitor.funcs

    def infer(self, node: TopLevel, /) -> list[Ty0]:
        ts = self.visit_TopLevel(node)
        ev = self.expr_visitor
        ev.uf.check()

        predicates: set[tuple[str, Ty0, DILocation]] = set()
        for name, ty, diloc in ev.predicates:
            try:
                ty = ev.uf.apply(ty)
            except RecursiveType as e:
                with get_adapter(bounds=diloc.get_bounds()) as adapter:
                    adapter.error(e.dump())
                raise e

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
                    with get_adapter(bounds=diloc.get_bounds()) as adapter:
                        adapter.error(f"cannot find an instance of {name} '{ty}'")
                    raise NoInstance(name, ty)
            predicates.add((name, ty, diloc))
        ev.predicates = predicates

        for f in ev.funcs:
            try:
                ev.funcs[f] = ev.uf.apply(ev.funcs[f])
            except RecursiveType as e:
                with get_adapter(bounds=ev.di_vars[f].loc.get_bounds()) as adapter:
                    adapter.error(e.dump())
                raise e

        return ts

    def visit_Decl(self, node: Decl) -> None:
        ev = self.expr_visitor
        ev.env[node.binding.var.name] = ev.visit(node.binding.e1)
        ev.di_vars[node.binding.var.name] = node.binding.var.metadata

    def visit_TopLevel(self, node: TopLevel):
        ts: list[Ty0] = []
        for decl_or_expr in node.decl_or_exprs:
            match decl_or_expr:
                case Decl():
                    self.visit_Decl(decl_or_expr)
                case DeclRec():
                    self.expr_visitor.visit_Function(decl_or_expr.f)
                case _:
                    ts.append(self.expr_visitor.visit(decl_or_expr, ty0_unit))
        return ts


class Monomorphization:
    __slots__ = 'uf',
    from ty import Ty, TyInt, TyFloat, TyBool, TyUnit, TyFun, TyTuple, TyArray

    def __init__(self, uf: UnionFind):
        self.uf = uf

    def visit(self, ty: Ty0, /):
        match ty:
            case TyCon():
                return self.visit_tycon(ty)
            case TyVar():
                match self.uf.apply(ty):
                    case TyCon() as tycon:
                        return self.visit_tycon(tycon)
                    case TyVar():
                        return Monomorphization.TyInt(), {ty}

    def visit_tycon(self, ty: TyCon, /) -> tuple[Ty, set[TyVar]]:
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
                    a, u = self.visit(a)
                    args.append(a)
                    us |= u
                return self.TyFun(*args), us
            case 'tuple', [_, _, *_]:
                us = set()
                args = []
                for a in ty.args:
                    a, u = self.visit(a)
                    args.append(a)
                    us |= u
                return self.TyTuple(args), us
            case 'array', [elem]:
                a, u = self.visit(elem)
                return self.TyArray(a), u
            case _:
                raise NotImplementedError(ty)
