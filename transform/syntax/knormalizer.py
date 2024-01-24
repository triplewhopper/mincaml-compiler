import contextlib
import logging
from collections.abc import Callable
from collections import ChainMap

import transform.knormal as kn
from .visitor import ExprVisitor
from .infer import Monomorphization
from .language import Expr, Lit, Var, Get, Unary, App, Binary, Semi, Tuple, Put, If, Let, LetRec, LetTuple, DeclRec, \
    Decl, TopLevel, Function, LetBinding
from .errors import ExternalVariableTypeError
from withbounds import WithBounds as WBs
from ty import TyFun, TyArray, TyTuple, TyInt, TyBool, Ty
from id import Id, LocalId, GlobalId, TmpId, tmp_id_factory
from .. import bind_logger
from typing import TypeVar, overload, Literal

get_adapter = bind_logger(logger=logging.getLogger(__name__))

T = TypeVar('T', bound=Ty)
K = kn.KNormal[Ty]

def insert_let(kn1: K, k: Callable[[Id], kn.KNormal[T]]) -> kn.KNormal[T]:
    if isinstance(kn1, kn.Ext):
        return k(kn1.name)
    elif isinstance(kn1, kn.Var):
        return k(kn1.name)
    x = next(tmp_id_factory)
    x.bounds = kn1.bounds
    with get_adapter(bounds=kn1.bounds) as adapter:
        adapter.info(f"generated fresh variable '%s' : '%s'. ", x, kn1.typ)
    kn2 = k(x)
    assert kn1.bounds.issubset(kn2.bounds)
    return kn.Let(kn.LetBinding(x, kn1, bounds=kn1.bounds), kn2, bounds=kn2.bounds)


class KNormalizer(ExprVisitor[K]):
    def __init__(self, mono: Monomorphization, funcs: dict[WBs[str], TyFun]):
        self.defs = ChainMap[str, WBs[str]]()
        self._mono = mono
        self._known_ext_funcs: dict[TyFun, set[GlobalId]] = {}  # prepared for closure conversion
        self._known_global_vars: dict[Ty, set[GlobalId]] = {}  # prepared for ir emission
        self._funcs = funcs.copy()

    @property
    def known_ext_funcs(self):
        """
        Set of external functions that should be converted to AppDir.
        Since functions must be fully applied in Min-Caml,
         all applications of external functions should be converted to AppDir.
        """
        return self._known_ext_funcs

    @property
    def known_global_vars(self):
        """
        Set of external arrays.
        """
        return self._known_global_vars

    @contextlib.contextmanager
    def _new_child_defs(self, defs: dict[str, WBs[str]]):
        self.defs = self.defs.new_child(defs)
        try:
            yield
        finally:
            self.defs = self.defs.parents

    def visit(self, node: Expr):
        x = super().visit(node)
        assert x.bounds == node.bounds
        return x

    def visit_Lit(self, node: Lit):
        return kn.Lit(node.lit)

    def visit_Var(self, node: Var):
        if node.name.val in self.defs:
            if node.name.val not in ChainMap(*self.defs.maps[:-1]):
                return kn.Var(GlobalId(node.name, self.defs[node.name.val]),
                              typ=self._mono.visit(node.ty0.result())[0])
            return kn.Var(LocalId(node.name, self.defs[node.name.val]), typ=self._mono.visit(node.ty0.result())[0])
        else:
            ty, _ = self._mono.visit(node.ty0.result())
            # if isinstance(ty, (TyArray, TyTuple)):
            #     res = kn.Ext(ExtId(node.name), typ=ty)
            #     self._known_global_vars.setdefault(ty, set()).add(res.name)
            #     return res
            # el
            if isinstance(ty, TyFun):
                res = kn.Ext(GlobalId(node.name), typ=ty)
                self._known_ext_funcs.setdefault(ty, set()).add(res.name)
                return res
            else:
                with get_adapter(bounds=node.bounds) as adapter:
                    adapter.error(f"external variable '{node}' does not have function type (got {ty})")
                raise ExternalVariableTypeError(node)

    def visit_Get(self, node: Get):
        array = self.visit(node.e1)

        def k1(a: Id):
            index = self.visit(node.e2)

            def k2(i: Id):
                assert isinstance(array.typ, TyArray) and isinstance(index.typ, TyInt)
                assert isinstance(i, (LocalId, TmpId))
                return kn.Get(a, i, typ=array.typ.elem, bounds=node.bounds)

            return insert_let(index, k2)

        return insert_let(array, k1)

    def visit_Unary(self, node: Unary):
        e = self.visit(node.e)

        def k(x: Id):
            assert isinstance(x, (LocalId, TmpId))
            op = kn.Unary.resolve_overloading(node.op, e.typ)
            return kn.Unary(op, x, bounds=node.bounds)

        return insert_let(e, k)

    def visit_App(self, node: App):
        callee = self.visit(node.callee)

        def k1(f: Id):
            def bind(xs: list[tuple[Id, K]], es: tuple[Expr, ...], i: int) -> K:
                if i == len(es):
                    assert isinstance(callee.typ, TyFun)
                    assert len(callee.typ.args) == len(xs)
                    assert all(k.typ == t for (_, k), t in zip(xs, callee.typ.args))
                    return kn.App(f, *(x for x, _ in xs), typ=callee.typ.ret, bounds=node.bounds)

                kn0 = self.visit(es[i])

                def k2(x: Id):
                    xs.append((x, kn0))
                    return bind(xs, es, i + 1)

                return insert_let(kn0, k2)

            return bind([], node.args, 0)

        return insert_let(callee, k1)

    def visit_Binary(self, node: Binary):
        e1 = self.visit(node.e1)
        e2 = self.visit(node.e2)
        assert e1.typ == e2.typ

        def k1(x1: Id):
            def k2(x2: Id):
                op = kn.Binary.resolve_overloading(node.op, e1.typ)
                return kn.Binary(op, x1, x2, bounds=node.bounds)

            return insert_let(e2, k2)

        return insert_let(e1, k1)

    def visit_Semi(self, node: Semi):
        return kn.Seq(*(self.visit(e) for e in node.es))

    def visit_Tuple(self, node: Tuple):
        def bind(xs: list[tuple[Id, K]], es: tuple[Expr, ...], i: int) -> K:
            if i == len(es):
                return kn.Tuple(*(x for x, _ in xs), typ=TyTuple(k.typ for _, k in xs), bounds=node.bounds)
            kn_i = self.visit(es[i])

            def k2(x: Id):
                xs.append((x, kn_i))
                return bind(xs, es, i + 1)

            return insert_let(kn_i, k2)

        return bind([], node.es, 0)

    def visit_Put(self, node: Put):
        array = self.visit(node.e1)

        def k1(a: Id):
            index = self.visit(node.e2)

            def k2(i: Id):
                value = self.visit(node.e3)

                def k3(v: Id):
                    assert isinstance(array.typ, TyArray)
                    assert isinstance(index.typ, TyInt)
                    assert array.typ.elem == value.typ
                    return kn.Put(a, i, v, bounds=node.bounds)

                return insert_let(value, k3)

            return insert_let(index, k2)

        return insert_let(array, k1)

    def visit_If(self, node: If):
        cond = self.visit(node.e1)
        assert cond.typ is TyBool()

        def k1(c: Id):
            br_true, br_false = self.visit(node.e2), self.visit(node.e3)
            return kn.If(c, br_true, br_false, bounds=node.bounds)

        return insert_let(cond, k1)

    def visit_LetBinding(self, b: LetBinding, is_global: bool =False) -> kn.LetBinding:
        if not is_global:
            return kn.LetBinding(LocalId(b.var, b.var), self.visit(b.e1), bounds=b.bounds)
        return kn.LetBinding(GlobalId(b.var, b.var), self.visit(b.e1), bounds=b.bounds)

    def visit_Let(self, node: Let):
        binding = self.visit_LetBinding(node.binding)
        with self._new_child_defs({node.binding.var.val: node.binding.var}):  # shadowing
            kn2 = self.visit(node.e2)

        return kn.Let(binding, kn2, bounds=node.bounds)

    def visit_LetTuple(self, node: LetTuple):
        kn1 = self.visit(node.e1)

        def k1(y: Id):
            self.defs = self.defs.new_child({x.val: x for x in node.xs})
            kn2 = self.visit(node.e2)
            self.defs = self.defs.parents
            assert isinstance(kn1.typ, TyTuple) and len(kn1.typ.elems) == len(node.xs)
            xs = tuple(LocalId(x, x) for x in node.xs)
            return kn.LetTuple(xs, kn1.typ.elems, y, kn2, bounds=node.bounds)

        return insert_let(kn1, k1)
    
    @overload
    def visit_Function(self, f: Function, is_global: Literal[False]=...) -> kn.Function[LocalId]:
        ...
    @overload
    def visit_Function(self, f: Function, is_global: Literal[True]) -> kn.Function[GlobalId]:
        ...
    
    def visit_Function(self, f: Function, is_global: bool=False) -> kn.Function[LocalId | GlobalId]:
        assert f.funct in self._funcs
        func_type = self._funcs[f.funct]
        assert len(func_type.args) == len(f.formal_args)
        formal_args = tuple(LocalId.create_definition(x) for x in f.formal_args)
        if is_global:
            self.defs[f.funct.val] = f.funct
            with self._new_child_defs({x.val: x for x in f.formal_args}):
                body = self.visit(f.e1)
            funct = GlobalId(f.funct, f.funct)
        else:
            with self._new_child_defs({f.funct.val: f.funct}):
                self.defs.update({x.val: x for x in f.formal_args})
                body = self.visit(f.e1)
            funct = LocalId(f.funct, f.funct)
            
        return kn.Function(funct, formal_args, body, typ=func_type, bounds=f.bounds)

    def visit_LetRec(self, node: LetRec):
        kn_func = self.visit_Function(node.f)
        with self._new_child_defs({node.f.funct.val: node.f.funct}):
            kn_e = self.visit(node.e2)
        return kn.LetRec(kn_func, kn_e, bounds=node.bounds)


class KNormalizerTopLevel:
    def __init__(self, expr_visitor: KNormalizer):
        self.expr_visitor = expr_visitor
        self.seq: dict[str, WBs[list[K | kn.LetBinding | kn.Function[GlobalId]]]] = {}

    @property
    def known_ext_funcs(self):
        return self.expr_visitor.known_ext_funcs

    @property
    def known_global_vars(self):
        return self.expr_visitor.known_global_vars

    def visit_Decl(self, decl: Decl):
        assert len(self.expr_visitor.defs.maps) == 1
        kn1 = self.expr_visitor.visit_LetBinding(decl.binding, is_global=True)
        assert isinstance(kn1.lhs, GlobalId)
        self.expr_visitor.known_global_vars.setdefault(kn1.rhs.typ, set()).add(kn1.lhs)
        self.expr_visitor.defs[decl.binding.var.val] = decl.binding.var
        self.seq[decl.bounds.filepath].val.append(kn1)

    def visit_DeclRec(self, decl: DeclRec):
        kn_func = self.expr_visitor.visit_Function(decl.f, is_global=True)
        assert isinstance(kn_func.funct, GlobalId)
        self.expr_visitor.known_global_vars.setdefault(kn_func.typ, set()).add(kn_func.funct)
        self.expr_visitor.defs[decl.f.funct.val] = decl.f.funct
        self.seq[decl.bounds.filepath].val.append(kn_func)

    def visit_TopLevel(self, toplevel: TopLevel):
        assert toplevel.bounds.filepath not in self.seq
        self.seq[toplevel.bounds.filepath] = WBs([], toplevel.bounds)
        for decl_or_expr in toplevel.decl_or_exprs:
            match decl_or_expr:
                case Decl():
                    self.visit_Decl(decl_or_expr)
                case DeclRec():
                    self.visit_DeclRec(decl_or_expr)
                case _:
                    kn1 = self.expr_visitor.visit(decl_or_expr)
                    self.seq[decl_or_expr.bounds.filepath].val.append(kn1)

def knormalize(knormalizer: KNormalizerTopLevel, **kwargs: TopLevel):
    kns: dict[str, list[kn.KNormal[Ty]| kn.LetBinding | kn.Function[GlobalId]]] = {}
    for filename, ast in kwargs.items():
        knormalizer.visit_TopLevel(ast)
        kns[filename] = knormalizer.seq[filename].val
    
    return kns