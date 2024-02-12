import logging
from collections.abc import Callable

import transform.knormal.language as kn
from .infer import Monomorphization
from .language import Expr, LitU, LitB, LitI, LitF, Var, Get, Unary, App, Binary, Semi, Tuple, Put, If, Let, LetRec, LetTuple, DeclRec, \
    Decl, TopLevel, Function, LetBinding
# from withbounds import WithBounds as WBs
from ty import TyFun, TyArray, TyTuple, TyInt, TyBool, Ty
from id import Id
from .. import bind_logger
from typing import TypeVar

get_adapter = bind_logger(logger=logging.getLogger(__name__))

T = TypeVar('T', bound=Ty)
K = kn.KNormal[Ty]

def insert_let(kn1: K, k: Callable[[Id], kn.KNormal[T]]) -> kn.KNormal[T]:
    # if isinstance(kn1, kn.Ext):
    #     return k(kn1.name)
    if isinstance(kn1, kn.Var):
        return k(kn1.name)
    x = Id()
    # x.bounds = kn1.bounds
    # with get_adapter(bounds=kn1) as adapter:
    #     adapter.info(f"generated fresh variable '%s' : '%s'. ", x, kn1.typ)
    kn2 = k(x)
    # assert kn1.bounds.issubset(kn2.bounds)
    return kn.Let(kn.LetBinding(x, kn1, is_tmp=True), kn2)


class KNormalizer:
    def __init__(self, mono: Monomorphization, funcs: dict[Id, TyFun]):
        # self.defs = ChainMap[str, WBs[str]]()
        self._mono = mono
        self._known_ext_funcs: dict[TyFun, set[Id]] = {}  # prepared for closure conversion
        self._known_global_vars: dict[Ty, set[Id]] = {}  # prepared for ir emission
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

    # @contextlib.contextmanager
    # def _new_child_defs(self, defs: dict[str, WBs[str]]):
    #     self.defs = self.defs.new_child(defs)
    #     try:
    #         yield
    #     finally:
    #         self.defs = self.defs.parents

    def visit(self, node: Expr) -> K:
        match node:
            case LitU():
                res = kn.LitU(node.metadata)
            case LitB():
                res = kn.LitB(node.metadata, node.lit)
            case LitI():
                res = kn.LitI(node.metadata, node.lit)
            case LitF():
                res = kn.LitF(node.metadata, node.lit)
            case Var():
                res = self.visit_Var(node)
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
        return res

    def visit_Var(self, node: Var):
        typ = self._mono.visit(node.ty0.result())[0]
        return kn.Var(node.name, typ=typ)
        # if node.name.val in self.defs:
        #     if node.name.val not in ChainMap(*self.defs.maps[:-1]):
        #         return kn.Var(GlobalId(node.name, self.defs[node.name.val]),
        #                       typ=self._mono.visit(node.ty0.result())[0])
        #     return kn.Var(LocalId(node.name, self.defs[node.name.val]), typ=self._mono.visit(node.ty0.result())[0])
        # else:
            # ty, _ = self._mono.visit(node.ty0.result())
            # if isinstance(ty, (TyArray, TyTuple)):
            #     res = kn.Ext(ExtId(node.name), typ=ty)
            #     self._known_global_vars.setdefault(ty, set()).add(res.name)
            #     return res
            # el
            # if isinstance(ty, TyFun):
            #     res = kn.Ext(GlobalId(node.name), typ=ty)
            #     self._known_ext_funcs.setdefault(ty, set()).add(res.name)
            #     return res
            # else:
            #     with get_adapter(bounds=node.bounds) as adapter:
            #         adapter.error(f"external variable '{node}' does not have function type (got {ty})")
            #     raise ExternalVariableTypeError(node)

    def visit_Get(self, node: Get):
        array = self.visit(node.e1)

        def k1(a: Id):
            index = self.visit(node.e2)

            def k2(i: Id):
                assert isinstance(array.typ, TyArray) and isinstance(index.typ, TyInt)
                assert isinstance(i, Id) and isinstance(a, Id)
                return kn.Get(a, i, typ=array.typ.elem)

            return insert_let(index, k2)

        return insert_let(array, k1)

    def visit_Unary(self, node: Unary):
        e = self.visit(node.e)

        def k(x: Id):
            assert isinstance(x, Id) and node.op in ('-', '-.')
            op = kn.Unary.resolve_overloading(node.op, e.typ)
            return kn.Unary(op, x, metadata=node.metadata)

        return insert_let(e, k)

    def visit_App(self, node: App):
        callee = self.visit(node.callee)

        def k1(f: Id):
            def bind(xs: list[tuple[Id, K]], es: tuple[Expr, ...], i: int) -> K:
                if i == len(es):
                    assert isinstance(callee.typ, TyFun)
                    assert all(k.typ == t for (_, k), t in zip(xs, callee.typ.args, strict=True))
                    return kn.App(f, *(x for x, _ in xs), typ=callee.typ.ret)

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
                return kn.Binary(op, x1, x2, metadata=node.metadata)

            return insert_let(e2, k2)

        return insert_let(e1, k1)

    def visit_Semi(self, node: Semi):
        return kn.Seq(*(self.visit(e) for e in node.es))

    def visit_Tuple(self, node: Tuple):
        def bind(xs: list[tuple[Id, K]], es: tuple[Expr, ...], i: int) -> K:
            if i == len(es):
                return kn.Tuple(*(x for x, _ in xs), typ=TyTuple(k.typ for _, k in xs))
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
                    assert isinstance(array.typ, TyArray) and isinstance(index.typ, TyInt)
                    assert array.typ.elem == value.typ
                    return kn.Put(a, i, v)

                return insert_let(value, k3)

            return insert_let(index, k2)

        return insert_let(array, k1)

    def visit_If(self, node: If):
        cond = self.visit(node.e1)
        assert cond.typ is TyBool()

        def k1(c: Id):
            br_true, br_false = self.visit(node.e2), self.visit(node.e3)
            return kn.If(c, br_true, br_false)

        return insert_let(cond, k1)

    def visit_LetBinding(self, b: LetBinding, is_global: bool =False) -> kn.LetBinding:
        return kn.LetBinding(b.var.name, self.visit(b.e1))

    def visit_Let(self, node: Let):
        binding = self.visit_LetBinding(node.binding)
        kn2 = self.visit(node.e2)
        return kn.Let(binding, kn2)

    def visit_LetTuple(self, node: LetTuple):
        kn1 = self.visit(node.e1)

        def k1(y: Id):
            kn2 = self.visit(node.e2)
            assert isinstance(kn1.typ, TyTuple) and len(kn1.typ.elems) == len(node.xs)
            xs = tuple(x.name for x in node.xs)
            return kn.LetTuple(xs, kn1.typ.elems, y, kn2)

        return insert_let(kn1, k1)

    
    def visit_Function(self, f: Function, is_global: bool=False) -> kn.Function:
        assert f.funct.name in self._funcs
        func_type = self._funcs[f.funct.name]
        assert len(func_type.args) == len(f.formal_args)
        formal_args = tuple(x.name for x in f.formal_args)
        body = self.visit(f.e1)
        funct = f.funct.name
        return kn.Function(funct, formal_args, body, typ=func_type)

    def visit_LetRec(self, node: LetRec):
        kn_func = self.visit_Function(node.f)
        kn_e = self.visit(node.e2)
        return kn.LetRec(kn_func, kn_e)


class KNormalizerTopLevel:
    def __init__(self, expr_visitor: KNormalizer):
        self.expr_visitor = expr_visitor
        self.seq: dict[str, list[K | kn.LetBinding | kn.Function]] = {}

    @property
    def known_ext_funcs(self):
        return self.expr_visitor.known_ext_funcs

    @property
    def known_global_vars(self):
        return self.expr_visitor.known_global_vars

    def visit_Decl(self, decl: Decl):
        kn1 = self.expr_visitor.visit_LetBinding(decl.binding, is_global=True)
        self.expr_visitor.known_global_vars.setdefault(kn1.rhs.typ, set()).add(kn1.lhs)
        return kn1

    def visit_DeclRec(self, decl: DeclRec):
        kn_func = self.expr_visitor.visit_Function(decl.f, is_global=True)
        self.expr_visitor.known_global_vars.setdefault(kn_func.typ, set()).add(kn_func.funct)
        return kn_func

    def visit_TopLevel(self, filename: str, toplevel: TopLevel):
        assert filename not in self.seq
        self.seq[filename] = []
        for decl_or_expr in toplevel.decl_or_exprs:
            match decl_or_expr:
                case Decl():
                    self.seq[filename].append(self.visit_Decl(decl_or_expr))
                case DeclRec():
                    self.seq[filename].append(self.visit_DeclRec(decl_or_expr))
                case _:
                    kn1 = self.expr_visitor.visit(decl_or_expr)
                    self.seq[filename].append(kn1)

def knormalize(knormalizer: KNormalizerTopLevel, **kwargs: TopLevel):
    kns: dict[str, list[kn.KNormal[Ty]| kn.LetBinding | kn.Function]] = {}
    for filename, ast in kwargs.items():
        knormalizer.visit_TopLevel(filename, ast)
        kns[filename] = knormalizer.seq[filename]
    
    return kns