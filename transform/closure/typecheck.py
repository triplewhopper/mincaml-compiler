from transform.closure.language import Program, Exp, Function, Cls, LetBinding, LitU, LitI, LitB, LitF, Var, Get, Unary, AppCls, AppDir, \
    Binary, Seq, Tuple, Put, If, Let, LetTuple, MakeCls
from ty import Ty, TyFun, TyUnit, TyInt, TyBool, TyFloat, TyTuple, TyArray
from id import Id
from collections import ChainMap
import contextlib
import unittest


class TypeCheck(unittest.TestCase):
    def __init__(self, env: dict[Id, Ty]):
        super(TypeCheck, self).__init__()
        self.env = ChainMap(env).new_child()
        self.is_definitely_not_cls: set[Id] = set(env)

    @contextlib.contextmanager
    def new_child_env(self, env: dict[Id, Ty]):
        self.env = self.env.new_child(env)
        try:
            yield
        finally:
            self.env = self.env.parents

    def lookup(self, x: Id):
        self.assertIn(x, self.env)
        return self.env[x]

    def test_program(self, prog: Program):
        for f in prog.fns:
            self.assertEqual(len(self.env.maps), 2, 'env should only have two maps: one for globals, one for builtins')
            self.assertNotIn(f.funct, self.env, f'function {f.funct} is already defined')
            self.env[f.funct] = f.typ
            if len(f.formal_fv) == 0:
                self.is_definitely_not_cls.add(f.funct)

        for f in prog.fns:
            self.visit_Function(f)

        for e in prog.exp_or_cls_or_letbindings:
            self.assertEqual(len(self.env.maps), 2)
            match e:
                case Exp():
                    self.assertIsInstance(e.typ, TyUnit)
                    self.visit(e)
                case Cls():
                    self.visit_Cls(e)
                case LetBinding():
                    self.visit_LetBinding(e)
                    self.assertIn(e.lhs, self.env)

    def visit(self, e: Exp[Ty]) -> Ty:
        match e:
            case LitU():
                self.assertIsInstance(e.typ, TyUnit)
                return TyUnit()
            case LitI():
                self.assertIsInstance(e.typ, TyInt)
                self.assertIsInstance(e.lit, int)
                return TyInt()
            case LitB():
                self.assertIsInstance(e.typ, TyBool)
                self.assertIsInstance(e.lit, bool)
                return TyBool()
            case LitF():
                self.assertIsInstance(e.typ, TyFloat)
                self.assertIsInstance(e.lit, float)
                return TyFloat()
            case Var():
                self.assertEqual(self.lookup(e.name), e.typ)
                return e.typ
            case Get():
                array_t = self.lookup(e.array)
                index_t = self.lookup(e.index)
                self.assertEqual(array_t, TyArray(e.typ))
                self.assertIsInstance(index_t, TyInt)
                return e.typ
            case Unary():
                y_t = self.lookup(e.y)
                self.assertEqual(TyFun(y_t, e.typ), e.op.typ)
                return e.typ
            case AppCls() | AppDir():
                if isinstance(e, AppDir):
                    self.assertIn(e.callee, self.is_definitely_not_cls)
                callee_t = self.lookup(e.callee)
                args_t = [self.lookup(arg) for arg in e.args]
                self.assertEqual(TyFun(*args_t, e.typ), callee_t)
                return e.typ
            case Binary():
                y1_t = self.lookup(e.y1)
                y2_t = self.lookup(e.y2)
                self.assertEqual(TyFun(y1_t, y2_t, e.typ), e.op.typ)
                return e.typ
            case Seq():
                for e1 in e.es[:-1]:
                    self.visit(e1)
                    self.assertIsInstance(e1.typ, TyUnit)
                self.assertEqual(e.es[-1].typ, e.typ)
                return self.visit(e.es[-1])
            case Tuple():
                self.assertEqual(e.typ, TyTuple([self.env[y] for y in e.ys]))
                return e.typ
            case Put():
                array_t = self.lookup(e.array)
                index_t = self.lookup(e.index)
                value_t = self.lookup(e.value)
                self.assertEqual(array_t, TyArray(value_t))
                self.assertIsInstance(index_t, TyInt)
                self.assertIsInstance(e.typ, TyUnit)
                return TyUnit()
            case If():
                cond_t = self.lookup(e.cond)
                self.assertIsInstance(cond_t, TyBool)
                self.assertEqual(self.visit(e.br_true), self.visit(e.br_false))
                self.assertEqual(e.br_true.typ, e.typ)
                return e.typ
            case Let():
                self.visit(e.binding.rhs)
                with self.new_child_env({e.binding.lhs: e.binding.rhs.typ}):
                    return self.visit(e.expr)
            case LetTuple():
                self.assertEqual(TyTuple(e.ts), self.lookup(e.y))
                with self.new_child_env(dict(zip(e.xs, e.ts))):
                    return self.visit(e.e)

            case MakeCls():
                self.visit_Cls(e.closure)
                with self.new_child_env({e.closure.entry.funct: e.closure.entry.typ}):
                    return self.visit(e.body)
            case _:
                raise NotImplementedError(e)

    def visit_LetBinding(self, binding: LetBinding):
        rhs_t = self.visit(binding.rhs)
        self.assertEqual(rhs_t, binding.rhs.typ)
        return rhs_t

    def visit_Cls(self, cls: Cls):
        self.assertIn(cls.entry.funct, self.env)
        self.assertEqual(len(cls.actual_fv), len(cls.entry.formal_fv))
        for actual_fv, (_, formal_fv_ty) in zip(cls.actual_fv, cls.entry.formal_fv):
            self.assertEqual(formal_fv_ty, self.lookup(actual_fv))

    def visit_Function(self, f: Function):
        self.assertIsInstance(f.typ, TyFun)
        with self.new_child_env({f.funct: f.typ}):
            self.assertEqual(len(f.formal_args), len(f.typ.args))
            self.assertSetEqual(set(f.formal_args) & set(fv for fv, _ in f.formal_fv), set())
            with self.new_child_env(dict(zip(f.formal_args, f.typ.args))):
                self.env.update(dict(f.formal_fv))
                self.assertEqual(self.visit(f.body), f.typ.ret)
