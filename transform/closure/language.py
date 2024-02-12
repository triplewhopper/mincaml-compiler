from opkinds import UnaryOpKind, BinaryOpKind
from id import Id
import transform.knormal.language as K
from ty import Ty, TyUnit, TyInt, TyFloat, TyBool, TyTuple, HasTypMixin, T
from metadata import DILocation
from collections.abc import Sequence

class Exp(HasTypMixin[T]):
    __slots__ = 'typ',

    def __init__(self, typ: T):
        super(Exp, self).__init__(typ)


class Cls:
    __slots__ = 'entry', 'actual_fv'

    def __init__(self, entry: 'Function', actual_fv: tuple[Id, ...]):
        assert isinstance(entry, Function)
        assert all(isinstance(x, Id) for x in actual_fv)
        assert len(entry.formal_fv) == len(actual_fv)
        self.entry = entry
        self.actual_fv = actual_fv

    def __str__(self):
        return f"{{entry={self.entry.funct}, actual_fv=( {', '.join(map(str, self.actual_fv))} )}}"


class Function:

    def __init__(self, fn: K.Function, body: Exp[Ty], formal_fv: tuple[tuple[Id, Ty], ...]):
        assert isinstance(fn, K.Function) and isinstance(body, Exp) and isinstance(formal_fv, tuple)
        assert body.typ == fn.body.typ
        for (v, t) in formal_fv:
            assert isinstance(v, Id) and isinstance(t, Ty)
        self.funct = fn.funct
        self.formal_args = fn.formal_args
        self.formal_fv = formal_fv
        self.body = body
        self.typ = fn.typ

    def iter_args(self):
        return zip(self.formal_args, self.typ.args)

    def __str__(self):
        if self.formal_fv:
            return f"let rec {self.funct} " \
                   f"{', '.join(f'({x}: {t})' for x, t in zip(self.formal_args, self.typ.args))} " \
                   f"(* formal_fv: {', '.join(f'({x}: {t})' for x, t in self.formal_fv)} *): {self.typ.ret} =\n{self.body}"
        return f"let rec {self.funct} " \
               f"{', '.join(f'({x}: {t})' for x, t in zip(self.formal_args, self.typ.args))}: {self.typ.ret} =\n{self.body}"

class Lit(Exp[K.L]):
    __slots__ = 'metadata',

    def __init__(self, metadata: DILocation, typ: K.L):
        super(Lit, self).__init__(typ)
        self.metadata = metadata


class LitU(Lit[TyUnit]):
    __slots__ = ()

    def __init__(self, lit: K.LitU):
        super().__init__(lit.metadata, lit.typ)

    def __str__(self):
        return "()"


class LitI(Lit[TyInt]):
    __slots__ = 'lit',
    __match_args__ = __slots__

    def __init__(self, lit: K.LitI):
        super().__init__(lit.metadata, lit.typ)
        self.lit = lit.lit

    def __str__(self):
        return str(self.lit)


class LitF(Lit[TyFloat]):
    __slots__ = 'lit',
    __match_args__ = __slots__

    def __init__(self, lit: K.LitF):
        super().__init__(lit.metadata, lit.typ)
        self.lit = lit.lit

    def __str__(self):
        return str(self.lit)


class LitB(Lit[TyBool]):
    __slots__ = 'lit',
    __match_args__ = __slots__

    def __init__(self, lit: K.LitB):
        super().__init__(lit.metadata, lit.typ)
        self.lit = lit.lit

    def __str__(self):
        return 'true' if self.lit else 'false'


class Var(Exp[Ty]):
    __slots__ = 'name',
    __match_args__ = __slots__

    def __init__(self, name: Id, typ: Ty):
        super(Var, self).__init__(typ)
        self.name = name

    def __str__(self):
        return str(self.name)


# class Ext(Exp[TyFun]):
#     __slots__ = 'name',
#     __match_args__ = 'name',
#
#     def __init__(self, ext: K.Ext):
#         assert isinstance(ext, K.Ext)
#         super(Ext, self).__init__(ext.bounds, ext.typ)
#         self.name = ext.name
#
#     def __str__(self):
#         return str(self.name)


class Get(Exp[Ty]):
    __slots__ = 'array', 'index'
    __match_args__ = __slots__

    def __init__(self, array: Id, index: Id, typ: Ty):
        super(Get, self).__init__(typ)
        self.array, self.index = array, index

    def __str__(self):
        return f"{self.array}.({self.index})"


class Unary(Exp[Ty]):
    __slots__ = 'op', 'y'
    __match_args__ = __slots__

    def __init__(self, op: UnaryOpKind, y: Id):
        super(Unary, self).__init__(op.typ.ret)
        self.op = op
        self.y = y

    def __str__(self):
        return f"({str(self.op)} {self.y})"


class AppDir(Exp[Ty]):
    __slots__ = 'callee', 'args'
    __match_args__ = __slots__

    def __init__(self, callee: 'Id', args: Sequence[Id], typ: Ty):
        super(AppDir, self).__init__(typ)
        self.callee, self.args = callee, tuple(args)

    def __str__(self):
        if not self.args:
            return f"({self.callee} (*no args*))"
        return f"({self.callee} {' '.join(map(str, self.args))})"


class AppCls(Exp[Ty]):
    __slots__ = 'callee', 'args'
    __match_args__ = __slots__

    def __init__(self, callee: Id, args: Sequence[Id], typ: Ty):
        super(AppCls, self).__init__(typ)
        self.callee, self.args = callee, tuple(args)

    def __str__(self):
        if not self.args:
            return f"({self.callee} (*no args*))"
        return f"({self.callee} (* as closure *) {' '.join(map(str, self.args))})"


class Binary(Exp[Ty]):
    __slots__ = 'op', 'y1', 'y2'
    __match_args__ = __slots__

    def __init__(self, op: BinaryOpKind, y1: Id, y2: Id):
        super(Binary, self).__init__(op.typ.ret)
        self.op, self.y1, self.y2 = op, y1, y2

    def __str__(self):
        return f"({self.y1} {self.op} {self.y2})"


class Tuple(Exp[TyTuple]):
    __slots__ = 'ys', 'name'
    __match_args__ = 'ys',

    def __init__(self, ys: Sequence[Id], typ: TyTuple):
        super(Tuple, self).__init__(typ)
        self.ys = tuple(ys)
        self.name: Id | None = None

    def __str__(self):
        return f"({', '.join(map(str, self.ys))})"


class Put(Exp[TyUnit]):
    __slots__ = 'array', 'index', 'value'
    __match_args__ = __slots__

    def __init__(self, array: Id, index: Id, value: Id):
        super(Put, self).__init__(TyUnit())
        self.array, self.index, self.value = array, index, value

    def __str__(self):
        return f"({self.array}.({self.index}) <- {self.value})"


class Seq(Exp[Ty]):
    __slots__ = 'es',
    __match_args__ = __slots__

    def __init__(self, *es: Exp[Ty]):
        assert all(isinstance(x, Exp) for x in es) and len(es) >= 2
        assert all(x.typ is TyUnit() for x in es[:-1])
        super(Seq, self).__init__(es[-1].typ)
        self.es = es

    def __str__(self):
        return f"({'; '.join(map(str, self.es))})"


class If(Exp[Ty]):
    __slots__ = 'cond', 'br_true', 'br_false'
    __match_args__ = __slots__

    def __init__(self, cond: Id, br_true: Exp[Ty], br_false: Exp[Ty]):
        assert isinstance(cond, Id) and isinstance(br_true, Exp) and isinstance(br_false, Exp)
        assert br_true.typ == br_false.typ
        super(If, self).__init__(br_true.typ)
        self.cond, self.br_true, self.br_false = cond, br_true, br_false

    def __str__(self):
        return f"(if {self.cond} then {self.br_true} else {self.br_false})"


class LetBinding:
    __slots__ = 'lhs', 'rhs', 'is_tmp'

    def __init__(self, lhs: Id, rhs: Exp[Ty], is_tmp: bool):
        assert isinstance(lhs, Id) and isinstance(rhs, Exp) and isinstance(is_tmp, bool)
        self.lhs, self.rhs, self.is_tmp = lhs, rhs, is_tmp

    def __repr__(self):
        return f"<val {self.lhs}: {self.rhs.typ}>"


class Let(Exp[T]):
    __slots__ = 'binding', 'expr'
    __match_args__ = __slots__

    def __init__(self, binding: LetBinding, expr: Exp[T]):
        assert isinstance(binding, LetBinding) and isinstance(expr, Exp)
        super(Let, self).__init__(expr.typ)
        self.binding, self.expr = binding, expr

    def __str__(self):
        if self.binding.is_tmp:
            return f"(let {self.binding.lhs} : {self.binding.rhs.typ} = {self.binding.rhs} in {self.expr})"
        return f"(let {self.binding.lhs} = {self.binding.rhs} in {self.expr})"


class LetTuple(Exp[T]):
    __slots__ = 'xs', 'ts', 'y', 'e'
    __match_args__ = __slots__

    def __init__(self, xs: Sequence[Id], ts: Sequence[Ty], y: Id, e: Exp[T]):
        assert isinstance(xs, Sequence) and isinstance(ts, Sequence) and isinstance(y, Id) and isinstance(e, Exp)
        assert len(xs) == len(ts)
        super(LetTuple, self).__init__(e.typ)
        self.xs, self.ts, self.y, self.e = xs, ts, y, e

    def __str__(self):
        return f"(let ({', '.join(f'({x}: {t})' for x, t in zip(self.xs, self.ts))}) = {self.y} in {self.e})"


class MakeCls(Exp[T]):
    __slots__ = 'closure', 'body'
    __match_args__ = __slots__

    def __init__(self, closure: Cls, body: Exp[T]):
        assert isinstance(closure, Cls) and isinstance(body, Exp)
        super(MakeCls, self).__init__(body.typ)
        self.closure, self.body = closure, body

    def __str__(self):
        return f"let[@closure] {self.closure.entry.funct} = {self.closure} in {self.body}"


#
# class Decl(HasBounds):
#     __slots__ = 'x', 'e'
#
#     def __init__(self, kn: K.Decl, e: Exp):
#         assert isinstance(kn, K.Decl) and isinstance(e, Exp)
#         assert e.typ == kn.e.typ
#         super(Decl, self).__init__(kn.bounds)
#         self.x, self.e = kn.x, e


class Program:
    __slots__ = 'fns', 'exp_or_cls_or_letbindings'

    def __init__(self, decls: tuple[Function, ...], *es: Exp[Ty] | LetBinding | Cls):
        assert all(isinstance(x, Function) for x in decls)
        assert all(isinstance(x, (Exp, LetBinding, Cls)) for x in es)
        assert all(x.typ is TyUnit() for x in es if isinstance(x, Exp))
        self.fns = decls
        self.exp_or_cls_or_letbindings = es

    def __str__(self):
        return "\n".join(map(str, self.fns)) + "\n" + "\n".join(map(str, self.exp_or_cls_or_letbindings))

