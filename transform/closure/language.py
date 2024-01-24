from bounds import HasBounds, Bounds, merge_bounds
from id import LocalId, Id
import transform.knormal.language as K
from typing import cast
from ty import Ty, TyFun, TyUnit, TyTuple, HasTypMixin, T


class Exp(HasBounds, HasTypMixin[T]):
    __slots__ = 'typ',

    def __init__(self, bounds: Bounds, typ: T):
        super(Exp, self).__init__(bounds)
        self.typ = typ


class Cls:
    __slots__ = 'entry', 'actual_fv'

    def __init__(self, entry: 'Function', actual_fv: tuple[LocalId, ...]):
        assert isinstance(entry, Function)
        assert all(isinstance(x, LocalId) for x in actual_fv)
        assert len(entry.formal_fv) == len(actual_fv)
        self.entry = entry
        self.actual_fv = actual_fv


class Function:

    def __init__(self, fn: K.Function[LocalId], body: Exp[Ty], formal_fv: tuple[tuple[LocalId, Ty], ...]):
        assert isinstance(fn, K.Function) and isinstance(body, Exp) and isinstance(formal_fv, tuple)
        assert body.typ == fn.body.typ
        for (v, t) in formal_fv:
            assert isinstance(v, LocalId) and isinstance(t, Ty)
        self.funct = fn.funct
        self.formal_args = fn.formal_args
        self.formal_fv = formal_fv
        self.typ = fn.typ
        self.bounds = fn.bounds

    def iter_args(self):
        return zip(self.formal_args, self.typ.args)

    def __repr__(self):
        return K.Function[LocalId].__repr__(cast(K.Function[LocalId], self))


class Lit(Exp[Ty]):
    __slots__ = 'lit',
    __match_args__ = __slots__

    def __init__(self, lit: K.Lit):
        assert isinstance(lit, K.Lit)
        super(Lit, self).__init__(lit.bounds, lit.typ)
        self.lit = lit.lit

    def __str__(self):
        return str(self.lit)

    def __repr__(self):
        return f"Lit({self.lit!r})"


class Var(Exp[Ty]):
    __slots__ = 'name',
    __match_args__ = __slots__

    def __init__(self, var: K.Var):
        assert isinstance(var, K.Var)
        super(Var, self).__init__(var.bounds, var.typ)
        self.name = var.name

    def __str__(self):
        return str(self.name)


class Ext(Exp[TyFun]):
    __slots__ = 'name',
    __match_args__ = 'name',

    def __init__(self, ext: K.Ext):
        assert isinstance(ext, K.Ext)
        super(Ext, self).__init__(ext.bounds, ext.typ)
        self.name = ext.name

    def __str__(self):
        return str(self.name)


class Get(Exp[Ty]):
    __slots__ = 'array', 'index'
    __match_args__ = 'array', 'index'

    def __init__(self, get: K.Get):
        assert isinstance(get, K.Get)
        super(Get, self).__init__(get.bounds, get.typ)
        self.array, self.index = get.array, get.index

    def __str__(self):
        return f"{self.array}.({self.index})"


class Unary(Exp[Ty]):
    __slots__ = 'op', 'y'
    __match_args__ = __slots__

    def __init__(self, unary: K.Unary):
        assert isinstance(unary, K.Unary)
        super(Unary, self).__init__(unary.bounds, unary.typ)
        self.op = unary.op
        self.y = unary.y

    def __str__(self):
        return f"({str(self.op)} {self.y})"


class AppDir(Exp[Ty]):
    __slots__ = 'callee', 'args'
    __match_args__ = __slots__

    def __init__(self, app: K.App):
        assert isinstance(app, K.App)
        super(AppDir, self).__init__(app.bounds, app.typ)
        self.callee, self.args = app.callee, app.args

    def __str__(self):
        if not self.args:
            return f"({self.callee} (*no args*))"
        return f"({self.callee} {' '.join(map(str, self.args))})"


class AppCls(Exp[Ty]):
    __slots__ = 'callee', 'args'
    __match_args__ = __slots__

    def __init__(self, app: K.App):
        assert isinstance(app, K.App)
        super(AppCls, self).__init__(app.bounds, app.typ)
        self.callee, self.args = app.callee, app.args

    def __str__(self):
        if not self.args:
            return f"({self.callee} (*no args*))"
        return f"({self.callee} {' '.join(map(str, self.args))})"


class Binary(Exp[Ty]):
    __slots__ = 'op', 'y1', 'y2'
    __match_args__ = 'op', 'y1', 'y2'

    def __init__(self, binary: K.Binary):
        assert isinstance(binary, K.Binary)
        super(Binary, self).__init__(binary.bounds, binary.typ)
        self.op, self.y1, self.y2 = binary.op, binary.y1, binary.y2

    def __str__(self):
        return f"({self.y1} {self.op} {self.y2})"


class Tuple(Exp[TyTuple]):
    __slots__ = 'ys', 'name'
    __match_args__ = 'ys',

    def __init__(self, tup: K.Tuple):
        assert isinstance(tup, K.Tuple)
        super(Tuple, self).__init__(tup.bounds, tup.typ)
        self.ys = tup.ys
        self.name: Id | None = None

    def __str__(self):
        return f"({', '.join(map(str, self.ys))})"


class Put(Exp[TyUnit]):
    __slots__ = 'array', 'index', 'value'
    __match_args__ = __slots__

    def __init__(self, put: K.Put):
        assert isinstance(put, K.Put)
        super(Put, self).__init__(put.bounds, put.typ)
        self.array, self.index, self.value = put.array, put.index, put.value

    def __str__(self):
        return f"({self.array}.({self.index}) <- {self.value})"


class Seq(Exp[Ty]):
    __slots__ = 'es',

    def __init__(self, *es: Exp[Ty]):
        assert all(isinstance(x, Exp) for x in es) and len(es) >= 2
        assert all(x.typ is TyUnit() for x in es[:-1])
        super(Seq, self).__init__(merge_bounds(*(e.bounds for e in es)), es[-1].typ)
        self.es = es


class If(Exp[Ty]):
    __slots__ = 'cond', 'br_true', 'br_false'
    __match_args__ = __slots__

    def __init__(self, kn: K.If, br_true: Exp[Ty], br_false: Exp[Ty]):
        assert isinstance(kn, K.If) and isinstance(br_true, Exp) and isinstance(br_false, Exp)
        assert br_true.typ == br_false.typ == kn.typ
        super(If, self).__init__(kn.bounds, kn.typ)
        self.cond, self.br_true, self.br_false = kn.cond, br_true, br_false


class LetBinding(HasBounds):
    __slots__ = 'lhs', 'rhs'

    def __init__(self, b: K.LetBinding, rhs: Exp[Ty]):
        assert isinstance(b, K.LetBinding) and isinstance(rhs, Exp)
        assert rhs.typ == b.rhs.typ
        super(LetBinding, self).__init__(b.bounds)
        self.lhs, self.rhs = b.lhs, rhs

    def __repr__(self):
        return f"<let {self.lhs}: {self.rhs.typ} @ {self.bounds}>"


class Let(Exp[T]):
    __slots__ = 'binding', 'expr'
    __match_args__ = __slots__

    def __init__(self, kn: K.Let[T], rhs: Exp[Ty], expr: Exp[T]):
        assert isinstance(kn, K.Let) and isinstance(rhs, Exp) and isinstance(expr, Exp)
        assert expr.typ == kn.expr.typ
        super(Let, self).__init__(kn.bounds, kn.typ)
        self.binding, self.expr = LetBinding(kn.binding, rhs), expr


class LetTuple(Exp[T]):
    __slots__ = 'xs', 'ts', 'y', 'e'
    __match_args__ = __slots__

    def __init__(self, kn: K.LetTuple[T], e: Exp[T]):
        assert isinstance(kn, K.LetTuple) and isinstance(e, Exp)
        assert e.typ == kn.e.typ
        super(LetTuple, self).__init__(kn.bounds, kn.typ)
        self.xs, self.ts, self.y, self.e = kn.xs, kn.ts, kn.y, e


class MakeCls(Exp[T]):
    __slots__ = 'closure', 'body'

    def __init__(self, let_rec: K.LetRec[T], closure: Cls, body: Exp[T]):
        assert isinstance(let_rec, K.LetRec) and isinstance(closure, Cls) and isinstance(body, Exp)
        super(MakeCls, self).__init__(let_rec.bounds, let_rec.typ)
        self.closure, self.body = closure, body


#
# class Decl(HasBounds):
#     __slots__ = 'x', 'e'
#
#     def __init__(self, kn: K.Decl, e: Exp):
#         assert isinstance(kn, K.Decl) and isinstance(e, Exp)
#         assert e.typ == kn.e.typ
#         super(Decl, self).__init__(kn.bounds)
#         self.x, self.e = kn.x, e


class Program(HasBounds):
    __slots__ = 'decl_or_cls_or_fns', 'es'

    def __init__(self, decls: tuple[LetBinding | Cls | Function, ...], *es: Exp[Ty], bounds: Bounds):
        assert all(isinstance(x, (LetBinding, Cls, Function)) for x in decls)
        assert all(isinstance(x, Exp) for x in es)
        assert all(x.typ is TyUnit() for x in es)
        super(Program, self).__init__(bounds)
        self.decl_or_cls_or_fns = decls
        self.es = es
