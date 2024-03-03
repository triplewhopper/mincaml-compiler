from transform.knormal import KNormal, LitU, LitI, LitB, LitF, Var, Get, Unary, App, Binary, Seq, Tuple, Put, If, Let, LetTuple, \
    LetRec, Function, LetBinding

from ty import TyTuple, Ty, T
from id import Id
import transform.closure as cl
import logging
from .. import bind_logger
from collections.abc import Generator


get_adapter = bind_logger(logger=logging.getLogger(__name__))


def fv(*xs: cl.Exp[Ty] | cl.LetBinding | cl.Cls):
    fv_visitor = cl.Fv()
    for x in reversed(xs):
        fv_visitor.visit(x)
    return fv_visitor.fv


class ClosureConverter:

    def __init__(self, known: dict[Id, Ty]):
        self.env: dict[Id, Ty] = {}
        self.known: dict[Id, cl.Function | None] = {k: None for k in known}
        self.global_vars: dict[Id, Ty] = {}
        self.toplevel_funcs: list[cl.Function] = []

    # @contextlib.contextmanager
    # def new_child_env(self, env: dict[Id, Ty]):
    #     self.env = self.env.new_child(env)
    #     try:
    #         yield
    #     finally:
    #         self.env = self.env.parents

    def convert(self, *es: KNormal[Ty] | Function | LetBinding) -> tuple[list[cl.Function], list[cl.Exp[Ty] | cl.Cls | cl.LetBinding]]:
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
                    # assert len(self.env.maps) == 1
                    func, zs = self.visit_Function(f)
                    self.env[funct] = func.typ
                    # self.global_vars.add(funct)
                    rest = list(deal(i + 1))
                    if funct in fv(*rest):
                        yield cl.Cls(func, tuple(zs))
                    yield from rest

                case LetBinding() as b:
                    # assert len(self.env.maps) == 1
                    rhs = self.visit(b.rhs, name=b.lhs)
                    self.env[b.lhs] = rhs.typ
                    self.global_vars[b.lhs] = rhs.typ
                    yield cl.LetBinding(b.lhs, rhs, b.is_tmp)
                    yield from deal(i + 1)

        b = list(deal(0))
        return self.toplevel_funcs.copy(), b

    def visit(self, e: KNormal[Ty] | cl.AppCls | cl.AppDir, /, *, name: Id | None = None) -> cl.Exp[Ty]:
        match e:
            case LitU():
                return cl.LitU(e)
            case LitI():
                return cl.LitI(e)
            case LitB():
                return cl.LitB(e)
            case LitF():
                return cl.LitF(e)
            case Var():
                return cl.Var(e.name, e.typ)
            case Get():
                return cl.Get(e.array, e.index, e.typ)
            case Unary():
                return cl.Unary(e.op, e.y)
            case App():
                return self.visit_App(e)
            case Binary():
                return cl.Binary(e.op, e.y1, e.y2)
            case Seq():
                return self.visit_Seq(e, name=name)
            case Tuple():
                return self.visit_Tuple(e, name=name)
            case Put():
                return cl.Put(e.array, e.index, e.value)
            case If():
                return self.visit_If(e)
            case Let():
                return self.visit_Let(e, name=name)
            case LetTuple():
                return self.visit_LetTuple(e, name=name)
            case LetRec():
                return self.visit_LetRec(e, name=name)
            case cl.AppCls() | cl.AppDir():
                return e
            case _:
                raise NotImplementedError(e)

    def visit_App(self, node: App):
        try:
            match self.known[node.callee]:
                case None:
                    return cl.AppDir(node.callee, node.args, node.typ)
                case _f:
                    # with get_adapter(bounds=node.callee.bounds) as adapter:
                    #     adapter.info(f"directly applying function '{node.callee}'")
                    return cl.AppDir(node.callee, node.args, node.typ)
        except KeyError:
            return cl.AppCls(node.callee, node.args, node.typ)

    def visit_Seq(self, node: Seq, /, *, name: Id | None = None):
        xs: list[cl.Exp[Ty]] = []
        for i in range(len(node.es) - 1):
            xs.append(self.visit(node.es[i]))
        xs.append(self.visit(node.es[-1], name=name))

        assert all(x.typ is e.typ for x, e in zip(xs, node.es))
        return cl.Seq(*xs)

    def visit_Tuple(self, node: Tuple, /, *, name: Id | None = None):
        x = cl.Tuple(node.ys, node.typ)
        x.name = name
        return x

    def visit_Put(self, node: Put, _):
        return cl.Put(node.array, node.index, node.value)

    def visit_If(self, node: If, /):
        b1 = self.visit(node.br_true)
        b2 = self.visit(node.br_false)

        return cl.If(node.cond, b1, b2)

    def visit_Let(self, node: Let[Ty], /, *, name: Id | None = None) -> cl.Let[Ty]:
        rhs = self.visit(node.binding.rhs, name=node.binding.lhs)
        self.env.update({node.binding.lhs: rhs.typ})
        expr = self.visit(node.expr, name=name)
        binding = cl.LetBinding(node.binding.lhs, rhs, node.binding.is_tmp)
        return cl.Let(binding, expr)

    def visit_LetTuple(self, node: LetTuple[T], /, *, name: Id | None = None):
        assert node.y in self.env
        y_ty = self.env[node.y]
        assert isinstance(y_ty, TyTuple) and y_ty.elems == node.ts
        self.env.update(zip(node.xs, node.ts))
        e = self.visit(node.e, name=name)
        # self.env = self.env.parents
        return cl.LetTuple(node.xs, node.ts, node.y, e)

    def visit_Function(self, f: Function) -> tuple[cl.Function, list[Id]]:
        toplevel_backup = self.toplevel_funcs.copy()
        # with self.new_child_env({f.funct: f.typ}):
        assert f.funct not in self.env or self.env[f.funct] == f.typ
        self.env[f.funct] = f.typ
        self.env.update(f.iter_args())
        self.known[f.funct] = None

        body1 = self.visit(f.body)

        zs = fv(body1).difference(f.formal_args).difference(self.global_vars)

        if len(zs) > 0:
            # def quoted(x: str):
            #     return f"'{x}'"

            # with get_adapter(bounds=f.bounds) as adapter:
            #     adapter.info(
            #         f"free variable(s) found in function {f.funct}: {', '.join(quoted(str(z)) for z in zs)}\n"
            #         f"function {f.funct} cannot be directly applied in fact.")

            self.toplevel_funcs = toplevel_backup
            del self.known[f.funct]
            body1 = self.visit(f.body)

        zs = list(fv(body1).difference({f.funct}.union(f.formal_args).union(self.global_vars)))
        zts = [(z, self.env[z]) for z in zs]

        func = cl.Function(f, body1, tuple(zts))
        self.toplevel_funcs.append(func)

        return func, zs

    def visit_LetRec(self, node: LetRec, /, *, name: Id | None = None):
        func, zs = self.visit_Function(node.f)
        # with self.new_child_env({node.f.funct: func.typ}):
        assert node.f.funct in self.env and self.env[node.f.funct] == func.typ
        # self.env[node.f.funct] = func.typ
        e2 = self.visit(node.e, name=name)
        if node.f.funct in fv(e2):
            return cl.MakeCls(cl.Cls(func, tuple(zs)), e2)
        else:
            # with get_adapter(bounds=node.f.funct.bounds) as adapter:
            #     adapter.info(f"eliminating closure {node.f.funct}")
            return e2
