import contextlib
from collections import ChainMap
from transform.knormal import KNormal, Lit, Var, Ext, Get, Unary, App, Binary, Seq, Tuple, Put, If, Let, LetTuple, \
    LetRec, Function, LetBinding

from ty import TyTuple, TyFun, Ty, T
from id import GlobalId, LocalId, Id
import transform.closure as cl
import logging
from .. import bind_logger
from collections.abc import Generator
from typing import TypeVar

G = TypeVar("G", GlobalId, LocalId)

get_adapter = bind_logger(logger=logging.getLogger(__name__))


def fv(*xs: cl.Exp[Ty] | cl.LetBinding | cl.Cls):
    fv_visitor = cl.Fv()
    for x in reversed(xs):
        fv_visitor.visit(x)
    return fv_visitor.fv


class ClosureConverter:

    def __init__(self, known: dict[TyFun, set[GlobalId]]):
        self.env: ChainMap[Id, Ty] = ChainMap()
        self.known: set[GlobalId | LocalId] = {x for v in known.values() for x in v}
        self.global_vars: set[LocalId] = set()
        self.toplevel_funcs: list[cl.Function] = []

    @contextlib.contextmanager
    def new_child_env(self, env: dict[Id, Ty]):
        self.env = self.env.new_child(env)
        try:
            yield
        finally:
            self.env = self.env.parents

    def convert(self, *es: KNormal[Ty] | Function[GlobalId] | LetBinding) \
            -> tuple[list[cl.Function], list[cl.Exp[Ty] | cl.Cls | cl.LetBinding]]:
        """
        Converts a KNormal expression into a list of functions and an expression.
        """

        def deal(i: int) -> Generator[cl.Exp[Ty] | cl.Cls | cl.LetBinding, None, None]:
            if i == len(es):
                return
            match es[i]:
                case KNormal() as e:
                    yield self.visit(e)
                    yield from deal(i + 1)

                case Function(funct=funct) as f:
                    assert len(self.env.maps) == 1
                    func, zs = self.visit_Function(f)
                    self.env[funct] = func.typ
                    # self.global_vars.add(funct)
                    rest = list(deal(i + 1))
                    if funct in fv(*rest):
                        yield cl.Cls(func, tuple(zs))
                    yield from rest

                case LetBinding() as b:
                    assert len(self.env.maps) == 1
                    rhs = self.visit(b.rhs, name=b.lhs)
                    self.env[b.lhs] = rhs.typ
                    self.global_vars.add(b.lhs)
                    yield cl.LetBinding(b, rhs)
                    yield from deal(i + 1)

                case e:
                    raise TypeError(e)
        b = list(deal(0))
        return self.toplevel_funcs.copy(), b

    def visit(self, e: KNormal[T], /, *, name: Id | None = None) -> cl.Exp[T]:
        return getattr(self, f"visit_{e.__class__.__name__}")(e, name=name)

    def visit_Lit(self, node: Lit, _):
        return cl.Lit(node)

    def visit_Var(self, node: Var, _):
        return cl.Var(node)

    def visit_Ext(self, node: Ext, _):
        if isinstance(node.typ, TyFun):
            self.known.add(node.name)
        return cl.Ext(node)

    def visit_Get(self, node: Get, _):
        return cl.Get(node)

    def visit_Unary(self, node: Unary, _):
        return cl.Unary(node)

    def visit_App(self, node: App, _):
        if node.callee in self.known:
            assert isinstance(node.callee, (GlobalId, LocalId))
            # with get_adapter(bounds=node.callee.bounds) as adapter:
            #     adapter.info(f"directly applying function '{node.callee}'")
            return cl.AppDir(node)
        else:
            return cl.AppCls(node)

    def visit_AppDir(self, node: App, _) -> cl.AppDir:
        """
        This method can be called because in visit_LetRec, there may be need to visit function's body one more time.
        """
        assert isinstance(node, cl.AppDir)
        return node

    def visit_AppCls(self, node: App, _) -> cl.AppCls:
        """This method can be called, due to the same reason as visit_AppDir."""
        assert isinstance(node, cl.AppCls)
        return node

    def visit_Binary(self, node: Binary, _) -> cl.Binary:
        return cl.Binary(node)

    def visit_Seq(self, node: Seq, /, *, name: Id | None = None):
        xs: list[cl.Exp[Ty]] = []
        for i in range(len(node.es) - 1):
            xs.append(self.visit(node.es[i]))
        xs.append(self.visit(node.es[-1], name=name))

        assert all(x.typ is e.typ for x, e in zip(xs, node.es))
        return cl.Seq(*xs)

    def visit_Tuple(self, node: Tuple, /, *, name: Id | None = None):
        x = cl.Tuple(node)
        x.name = name
        return x

    def visit_Put(self, node: Put, _):
        return cl.Put(node)

    def visit_If(self, node: If, _):
        b1 = self.visit(node.br_true)
        b2 = self.visit(node.br_false)

        return cl.If(node, b1, b2)

    def visit_Let(self, node: Let[T], /, *, name: Id | None = None) -> cl.Let[T]:
        rhs = self.visit(node.binding.rhs, name=node.binding.lhs)
        with self.new_child_env({node.binding.lhs: rhs.typ}):
            expr = self.visit(node.expr, name=name)
        return cl.Let(node, rhs, expr)

    def visit_LetTuple(self, node: LetTuple[T], /, *, name: Id | None = None):
        assert node.y in self.env
        y_ty = self.env[node.y]
        assert isinstance(y_ty, TyTuple) and y_ty.elems == node.ts
        self.env = self.env.new_child(dict(zip(node.xs, node.ts)))
        e = self.visit(node.e, name=name)
        self.env = self.env.parents
        return cl.LetTuple(node, e)

    def visit_Function(self, f: Function[LocalId]) -> tuple[cl.Function, list[LocalId]]:
        toplevel_backup = self.toplevel_funcs.copy()
        with self.new_child_env({f.funct: f.typ}):
            self.env.update(f.iter_args())
            self.known.add(f.funct)
            body1 = self.visit(f.body)

            zs = fv(body1).difference(f.formal_args).difference(self.global_vars)

            if len(zs) > 0:
                def quoted(x: str):
                    return f"'{x}'"

                with get_adapter(bounds=f.bounds) as adapter:
                    adapter.info(
                        f"free variable(s) found in function {f.funct}: {', '.join(quoted(str(z)) for z in zs)}\n"
                        f"function {f.funct} cannot be directly applied in fact.")

                self.toplevel_funcs = toplevel_backup
                self.known.remove(f.funct)
                body1 = self.visit(f.body)

            zs = list(fv(body1).difference({f.funct}.union(f.formal_args).union(self.global_vars)))
            zts = [(z, self.env[z]) for z in zs]

            func = cl.Function(f, body1, tuple(zts))
            self.toplevel_funcs.append(func)

        return func, zs

    def visit_LetRec(self, node: LetRec[T], /, *, name: Id | None = None):
        func, zs = self.visit_Function(node.f)
        with self.new_child_env({node.f.funct: func.typ}):
            e2 = self.visit(node.e, name=name)
        if node.f.funct in fv(e2):
            return cl.MakeCls(node, cl.Cls(func, tuple(zs)), e2)
        else:
            # with get_adapter(bounds=node.f.funct.bounds) as adapter:
            #     adapter.info(f"eliminating closure {node.f.funct}")
            return e2

# class ClosureConverterTopLevel(KNormalVisitor[ClosureConverter]):
#     def __init__(self, expr_visitor: ClosureConverter):
#         super().__init__(expr_visitor)
#
#     def visit_Decl(self, decl: Decl):
#         e = self.expr_visitor.visit(decl.e)
#         assert len(self.expr_visitor.env.maps) == 1
#         self.expr_visitor.env[decl.x] = decl.e.typ
#         return cl.Decl(decl, e)
#
#     def visit_DeclRec(self, decl_rec: DeclRec):
#         func, zs = self.expr_visitor.visit_Function(decl_rec.f)
#         self.expr_visitor.env[decl_rec.f.funct] = func.typ
#         return func, zs
#
#     def visit_TopLevel(self, toplevel: TopLevel) -> cl.Program:
#         decls = []
#         exprs = []
#         for i, decl_or_expr in enumerate(toplevel.decl_or_exprs):
#             if isinstance(decl_or_expr, DeclRec):
#                 func, zs = self.visit_DeclRec(decl_or_expr)
#                 if decl_or_expr.f.funct in fv(*toplevel.decl_or_exprs[i + 1:]):
#                     decls.append(cl.Cls(func, tuple(zs)))
#             elif isinstance(decl_or_expr, Decl):
#                 decls.append(self.visit_Decl(decl_or_expr))
#             else:
#                 exprs.append(self.expr_visitor.visit(decl_or_expr))
#         return cl.Program(tuple(decls), *exprs, bounds=toplevel.bounds)
