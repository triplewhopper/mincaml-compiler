from typing import Callable, Self
from collections.abc import Iterable
from .visitor import ExpVisitor
from .language import Exp, Var, AppDir, Seq, Let, LetBinding, LetTuple, MakeCls, Cls, AppCls, Binary, Unary, If, Put, Tuple, Get, Lit, Ext
from id import LocalId, Id


class Fv:

    def __init__(self):
        self.__fv: set[LocalId] = set()

    @property
    def fv(self) -> frozenset[LocalId]:
        assert all(isinstance(x, LocalId) for x in self.__fv)
        return frozenset(self.__fv)

    # def __do_nothing(self, node: Exp) -> None:
    #     pass

    # @staticmethod
    # def __gen_fv_fn(acc_fvs: tuple[str, ...] = (), iter_acc_fvs: tuple[str, ...] = (), visits: tuple[str, ...] = ()):
    #     def f(self: Self, node: Exp) -> None:
    #         for x in acc_fvs:
    #             y = getattr(node, x)
    #             assert isinstance(y, Id)
    #             y.acc_fv(self.__fv)

    #         for x in iter_acc_fvs:
    #             y = getattr(node, x)
    #             assert isinstance(y, Iterable)
    #             for z in y:
    #                 assert isinstance(z, Id)
    #                 z.acc_fv(self.__fv)

    #         for x in visits:
    #             y = getattr(node, x)
    #             assert isinstance(y, Exp)
    #             self.visit(y)

    #     return f
    
    def visit(self, node: Exp | Cls | LetBinding) -> None:
        def acc_fvs(*xs: Id):
            self.__fv.update(x for x in xs if isinstance(x, LocalId))
        match node:
            case Lit() | Ext():
                ...
            case Var(name):
                self.__fv.add(name)
            case Get(array, index):
                acc_fvs(array, index)
            case Unary(_, y):
                if isinstance(y, LocalId):
                    self.__fv.add(y)
            case AppCls(callee, args):
                acc_fvs(callee, *args)
            case AppDir(args=args):
                acc_fvs(*args)
            case Binary(_, y1, y2):
                acc_fvs(y1, y2)
            case Seq(es=es):
                for e in reversed(es): self.visit(e)
            case Tuple(ys):
                acc_fvs(*ys)
            case Put(array, index, value):
                acc_fvs(array, index, value)
            case If(cond, br_true, br_false):
                if isinstance(cond, LocalId): self.__fv.add(cond)
                self.visit(br_true)
                self.visit(br_false)
            case Let(binding, expr):
                self.visit(expr)
                self.__fv.discard(binding.lhs)
                self.visit(binding.rhs)
            case LetTuple(xs=xs, y=y, e=e):
                self.visit(e)
                self.__fv.difference_update(xs)
                if isinstance(y, LocalId): self.__fv.add(y)
            case MakeCls(closure=closure, body=body):
                self.visit(body)
                self.__fv.update(closure.actual_fv)
                self.__fv.discard(closure.entry.funct)
            case Cls(actual_fv=actual_fv, entry=entry):
                self.__fv.update(actual_fv)
                self.__fv.discard(entry.funct)
            case LetBinding(lhs=lhs, rhs=rhs):
                self.__fv.discard(lhs)
                self.visit(rhs)
            case _:
                raise ValueError(node)

    # visit_Lit = __do_nothing

    # def visit_Var(self, node: Var) -> None:
    #     self.__fv.add(node.name)

    # visit_Ext = __do_nothing
    # # visit_ExtArray = __do_nothing
    # # visit_ExtFun = __do_nothing

    # visit_Get = __gen_fv_fn(('array', 'index'))

    # visit_Unary = __gen_fv_fn(('y',))

    # visit_AppCls = __gen_fv_fn(('callee',), ('args',))

    # def visit_AppDir(self, node: AppDir):
    #     for x in node.args:
    #         x.acc_fv(self.__fv)

    # visit_Binary = __gen_fv_fn(('y1', 'y2'))

    # def visit_Seq(self, node: Seq) -> None:
    #     for e in reversed(node.es):
    #         self.visit(e)

    # visit_Tuple = __gen_fv_fn((), iter_acc_fvs=('ys',))

    # visit_Put = __gen_fv_fn(('array', 'index', 'value'))

    # visit_If = __gen_fv_fn(('cond',), visits=('br_true', 'br_false'))

    # def visit_Let(self, node: Let) -> None:
    #     self.visit(node.expr)
    #     node.binding.lhs.rm_fv(self.__fv)
    #     self.visit(node.binding.rhs)

    # def visit_LetBinding(self, binding: LetBinding) -> None:
    #     binding.lhs.rm_fv(self.__fv)
    #     self.visit(binding.rhs)

    # def visit_LetTuple(self, node: LetTuple) -> None:
    #     self.visit(node.e)
    #     for x in node.xs:
    #         self.__fv.discard(x)
    #     node.y.acc_fv(self.__fv)

    # def visit_MakeCls(self, node: MakeCls) -> None:
    #     self.visit(node.body)
    #     self.__fv.update(node.closure.actual_fv)
    #     self.__fv.discard(node.closure.entry.funct)

    # def visit_Cls(self, c: Cls) -> None:
    #     self.__fv.update(c.actual_fv)
    #     self.__fv.discard(c.entry.funct)
