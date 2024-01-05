from syntax import *
from ty0 import *
import ty
from typing import List, Dict, Set, FrozenSet
from collections import ChainMap
from functools import lru_cache
from pyparsing import col, lineno
import logging

logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(name)s - %(levelname)s - %(message)s')
logger = logging.getLogger(__name__)


class InferError(Exception):
    def __init__(self, bounds: tuple[int, int] = None):
        super().__init__()
        self._s = None
        self._bounds = bounds

    def set_bounds(self, bounds: tuple[int, int]):
        assert self._bounds is None
        self._bounds = bounds

    def set_s(self, s: bytes):
        assert self._s is None
        self._s = s

    def __str__(self):
        assert isinstance(self._bounds, tuple) and isinstance(self._s, bytes)
        ln = WithBounds(None, self._bounds).lineno(self._s)
        cl = WithBounds(None, self._bounds).col(self._s)
        line = f"line {ln}" if isinstance(ln, int) else f"lines {ln[0]}-{ln[1]}"
        character = f"character {cl}" if isinstance(cl, int) else f"characters {cl[0]}-{cl[1]}"
        return f"{line}, {character}:"


class UnifyError(InferError):
    def __init__(self, t1: Ty0, t2: Ty0, bounds: tuple[int, int] = None):
        super().__init__()
        self.t1 = t1
        self.t2 = t2
        self._s = None
        self._bounds = bounds

    def __str__(self):
        return super().__str__() + f"\ncannot unify {self.t1} and {self.t2}"


class RecursiveType(InferError):
    def __init__(self, t: TyVar, ty: Ty0, bounds: tuple[int, int] = None):
        super().__init__()
        self.t = t
        self.ty = ty
        self._s = None
        self._bounds = bounds

    def __str__(self):
        return super().__str__() + f"\nrecursive type '{self.t}' = '{self.ty}'"


class UnionFind:
    def __init__(self):
        self._parent: dict[Ty0, Ty0] = {}
        self._rank: dict[Ty0, int] = {}
        self._rp: dict[Ty0, TyCon] = {}

    def find(self, t: Ty0) -> Ty0:
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

    def merge(self, t1: Ty0, t2: Ty0, bounds: tuple[int, int] = None):
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

    def rp(self, t: Ty0) -> TyCon | None:
        return self._rp.get(self.find(t))

    def apply(self, t: Ty0) -> Ty0:
        if isinstance(t, TyCon):
            return TyCon(t.name, *[self.apply(a) for a in t.args])
        elif isinstance(t, TyVar):
            f = self.find(t)
            if (rp := self.rp(f)) is not None:
                if self.occurs_in(t, rp):
                    raise RecursiveType(t, rp)
                else:
                    return self.apply(rp)
            else:
                return t
        else:
            raise NotImplementedError()

    def occurs_in(self, t1: TyVar, t2: Ty0) -> bool:
        assert isinstance(t1, TyVar) and isinstance(t2, Ty0)
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
        families: Dict[Ty0, List[Ty0]] = {}
        for t in self._parent:
            f = self.find(t)
            families.setdefault(f, []).append(t)
        for v in families.values():
            v.sort(key=lambda t: -100 if isinstance(t, TyCon) else 0)
        return "\n".join(
            f"{f}: {', '.join(str(t) for t in families[f])}" for f in families
        )

    def check(self):
        families: Dict[Ty0, List[Ty0]] = {}
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

    def __init__(self, polys: FrozenSet[TyVar], qt: Ty0):
        assert isinstance(qt, Ty0)
        self._polys = polys
        self._ty0 = qt
        assert qt.tv.issuperset(polys)

    def __str__(self):
        return f"{' '.join(str(v) for v in self._polys)}. {self._ty0}"

    @staticmethod
    def from_ty0(ty: Ty0) -> 'Ty0Scheme':
        return Ty0Scheme(frozenset(), ty)

    @staticmethod
    def quantify(vs: Set[TyVar], qt: Ty0) -> 'Ty0Scheme':
        return Ty0Scheme(qt.tv.intersection(vs), qt)

    def apply_with(self, uf: UnionFind):
        ty0 = uf.apply(self._ty0)
        return Ty0Scheme(ty0.tv.intersection(self._polys), ty0)

    def monomorphize_with(self, mono: 'Monomorphization') -> ty.Ty:
        return mono.visit(self._ty0)

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


class Typing(NodeVisitor):
    def __init__(self, source: bytes):
        self.env: ChainMap[str, Ty0] = ChainMap()
        a = TyVar()
        array_make_sc = Ty0Scheme(frozenset([a]), ty0_fun(ty0_int, a, ty0_array(a)))
        self.ext: dict[str, Ty0Scheme] = {"Array.make": array_make_sc, "Array.create": array_make_sc}
        del a, array_make_sc

        self.predicates: set[(str, Ty0)] = set()
        self.funcs: dict[WithBounds[str], Ty0] = {}
        self.uf = UnionFind()
        self.__s = source

    def infer(self, node: Node) -> Ty0:
        t = self.visit(node)
        self.uf.check()
        t = self.uf.apply(t)
        predicates = set()
        for name, ty in self.predicates:
            ty = self.uf.apply(ty)
            match name, ty:
                case 'Num', TyCon('int' | 'float', _):
                    ...
                case 'Eq', TyCon('int' | 'float' | 'bool', _):
                    ...
                case 'Ord', TyCon('int' | 'float', _):
                    ...
                case ('Num' | 'Eq' | 'Ord'), TyVar():
                    logger.warning(f"uninstantiated type variable {ty} in {name} {ty}")
                case _:
                    raise TypeError(f"cannot find an instance of {name} '{ty}'")
            predicates.add((name, ty))
        self.predicates = predicates

        for k in self.ext:
            v = self.ext[k]
            self.ext[k] = v.apply_with(self.uf)

        for f in self.funcs:
            self.funcs[f] = self.uf.apply(self.funcs[f])

        return t

    def unify(self, t1: Ty0, t2: Ty0, bounds: tuple[int, int] = None):
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

    def visit(self, node: Node) -> Ty0:
        t = super().visit(node)
        assert isinstance(t, Ty0)
        return t

    def visit_Lit(self, node: Lit) -> Ty0:
        match node.val:
            # bool is a subclass of int, so we need to check bool first.
            case bool():
                return ty0_bool
            case int():
                return ty0_int
            case float():
                return ty0_float
            case '()':
                return ty0_unit
            case _:
                raise NotImplementedError()

    def visit_Var(self, node: Var) -> Ty0:
        try:
            node.tyvar = self.env[node.name.val]
            node.is_ext = False
            return node.tyvar
        except KeyError:
            node.is_ext = True
            try:
                node.tyvar = self.ext[node.name.val].instantiate()
                return node.tyvar
            except KeyError:
                logger.info(f"line {node.name.lineno(self.__s)}: variable '{node}' assumed as external")
                node.tyvar = TyVar()
                self.ext[node.name.val] = Ty0Scheme.from_ty0(node.tyvar)
                return node.tyvar

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
                self.predicates.add(('Num', t))
                return t
            case '-.':
                self.unify(t, ty0_float, node.e.bounds)
                return ty0_float
            case _:
                raise NotImplementedError()

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
            case '+' | '-':
                self.predicates.add(('Num', t1))
                self.predicates.add(('Num', t2))
                self.unify(t1, t2)
                return t1
            case '+.' | '-.' | '*.' | '/.':
                self.unify(t1, ty0_float, node.e1.bounds)
                self.unify(t2, ty0_float, node.e2.bounds)
                return ty0_float
            case '=' | '<>':
                self.predicates.add(('Eq', t1))
                self.predicates.add(('Eq', t2))
                self.unify(t1, t2, node.op.bounds)
                return ty0_bool
            case '<' | '>' | '<=' | '>=':
                self.predicates.add(('Ord', t1))
                self.predicates.add(('Ord', t2))
                self.unify(t1, t2, node.op.bounds)
                return ty0_bool
            # case ';':
            #     self.unify(t1, ty0_unit, node.e1.bounds)
            #     return t2
            case _:
                raise NotImplementedError()

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
        t1 = self.visit(node.e1)
        self.env = self.env.new_child(m={node.x.val: t1})
        t2 = self.visit(node.e2)
        self.env = self.env.parents
        return t2

    def visit_LetRec(self, node: LetRec) -> Ty0:
        f, e = node.f, node.e
        ty_args = [TyVar() for _ in f.formal_args]
        ty_ret = TyVar()
        ty_func = ty0_fun(*ty_args, ty_ret)
        assert f.funct not in self.funcs
        self.funcs[f.funct] = ty_func
        self.env = self.env.new_child(m={f.funct.val: ty_func, **{x.val: t for x, t in zip(f.formal_args, ty_args)}})
        # if there is an argument that has the same name as the function, then the function itself is shadowed.
        ty_body = self.visit(f.body)
        self.unify(ty_ret, ty_body, f.body.bounds)
        self.env = self.env.parents.new_child(m={f.funct.val: ty_func})
        t = self.visit(e)
        self.env = self.env.parents
        return t

    def visit_LetTuple(self, node: LetTuple):
        t1 = self.visit(node.e1)
        ts = [TyVar() for _ in node.xs]
        self.unify(t1, ty0_tuple(*ts), node.e1.bounds)
        self.env = self.env.new_child(m={x.val: t for x, t in zip(node.xs, ts)})
        t2 = self.visit(node.e2)
        self.env = self.env.parents
        return t2


class Monomorphization(Ty0Visitor):
    __slots__ = ['uf']

    def __init__(self, uf: UnionFind):
        self.uf = uf

    def visit(self, t: Ty0) -> ty.Ty:
        return super().visit(t)

    @lru_cache(maxsize=128)
    def visit_tycon(self, t: TyCon) -> ty.Ty:
        match t.name:
            case 'int':
                assert len(t.args) == 0
                return ty.TyInt()
            case 'float':
                assert len(t.args) == 0
                return ty.TyFloat()
            case 'bool':
                assert len(t.args) == 0
                return ty.TyBool()
            case 'unit':
                assert len(t.args) == 0
                return ty.TyUnit()
            case '->':
                assert len(t.args) >= 2
                return ty.TyFun(*[self.visit(a) for a in t.args])
            case 'tuple':
                assert len(t.args) >= 2
                return ty.TyTuple(self.visit(a) for a in t.args)
            case 'array':
                assert len(t.args) == 1
                return ty.TyArray(self.visit(t.args[0]))
            case _:
                raise NotImplementedError()

    def visit_tyvar(self, t: TyVar) -> ty.Ty:
        t = self.uf.apply(t)
        if isinstance(t, TyCon):
            return self.visit(t)
        else:
            logger.warning(f"uninstantiated type variable {t}: assumed as int")
            return ty.TyInt()
