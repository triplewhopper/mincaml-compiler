# from .visitor import ExpVisitor
from .language import Exp, Var, AppDir, Seq, Let, LetBinding, LetTuple, MakeCls, Cls, AppCls, Binary, Unary, If, Put, Tuple, Get, Lit
from id import Id
from ty import Ty


class Fv:

    def __init__(self):
        self.__fv: set[Id] = set()

    @property
    def fv(self) -> frozenset[Id]:
        assert all(isinstance(x, Id) for x in self.__fv)
        return frozenset(self.__fv)
    
    def visit(self, node: Exp[Ty] | Cls | LetBinding, /) -> None:
        def acc_fvs(*xs: Id):
            self.__fv.update(xs)
        match node:
            case Lit():
                ...
            case Var(name):
                self.__fv.add(name)
            case Get(array, index):
                acc_fvs(array, index)
            case Unary(_, y):
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
                self.__fv.add(cond)
                self.visit(br_true)
                self.visit(br_false)
            case Let(binding, expr):
                self.visit(expr)
                self.__fv.discard(binding.lhs)
                self.visit(binding.rhs)
            case LetTuple(xs=xs, y=y, e=e):
                self.visit(e)
                self.__fv.difference_update(xs)
                self.__fv.add(y)
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
