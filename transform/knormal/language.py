from typing import Literal, overload, TypeVar, Generic

from opkinds import literal_unary, literal_binary, BinaryOpKind, UnaryOpKind
# from id import LocalId, GlobalId, Id, TmpId
from id import Id
from ty import Ty, TyTuple, TyFun, TyArray, TyBool, TyInt, TyFloat, TyUnit, HasTypMixin as _HasTyp, T
from withbounds import WithBounds as WBs
from bounds import Bounds, HasBounds, merge_bounds


# class KNormal(HasBounds, _HasTyp[T]):
#     __slots__ = 'typ'

#     def __init__(self, bounds: Bounds, typ: T):
#         HasBounds.__init__(self, bounds)
#         _HasTyp[T].__init__(self, typ)
class KNormal(_HasTyp[T]):
    __slots__ = 'typ'

    def __init__(self, typ: T):
        _HasTyp[T].__init__(self, typ)

class Lit(KNormal[TyBool | TyInt | TyFloat | TyUnit]):
    __slots__ = 'lit'

    def __init__(self, lit: WBs[bool | int | float | Literal['()']], /):
        assert isinstance(lit, WBs)
        match lit.val:
            case bool():
                super(Lit, self).__init__(lit.bounds, TyBool())
            case int():
                super(Lit, self).__init__(lit.bounds, TyInt())
            case float():
                super(Lit, self).__init__(lit.bounds, TyFloat())
            case "()":
                super(Lit, self).__init__(lit.bounds, TyUnit())
        self.lit = lit

    @staticmethod
    def unit_with_bounds(bounds: Bounds):
        return Lit(WBs('()', bounds))

    def __str__(self):
        match self.lit.val:
            case True:
                return "true"
            case False:
                return "false"
            case _:
                return str(self.lit.val)


class Var(KNormal[Ty]):
    __slots__ = 'name'

    # def __init__(self, name: LocalId | GlobalId, /, *, typ: Ty):
    #     assert (isinstance(name, LocalId) and not name.is_definition or
    #             isinstance(name, GlobalId) and not name.is_external)
    #     super(Var, self).__init__(name.bounds, typ)
    #     self.name = name
    def __init__(self, name: Id, /, *, typ: Ty):
        assert isinstance(name, Id)
        super(Var, self).__init__(name.bounds, typ)
        self.name = name

    def __str__(self):
        return self.name.val.val


class Ext(KNormal[TyArray | TyFun | TyTuple]):
    __slots__ = 'name'

    def __init__(self, name: GlobalId, /, *, typ: TyArray | TyFun | TyTuple):
        assert isinstance(name, GlobalId) and isinstance(typ, (TyArray, TyFun, TyTuple))
        super(Ext, self).__init__(name.bounds, typ)
        self.name = name

    def __str__(self):
        return self.name.__str__()


class Get(KNormal[Ty]):
    __slots__ = 'array', 'index'

    def __init__(self, arr: Id, idx: Id, /, *, typ: Ty, bounds: Bounds):
        super(Get, self).__init__(bounds, typ)
        assert isinstance(arr, Id) and isinstance(idx, Id)
        self.array = arr
        self.index = idx

    def __str__(self):
        return f"{self.array}.({self.index})"


class Unary(KNormal[Ty]):
    __slots__ = 'op', 'y'

    @staticmethod
    @overload
    def resolve_overloading(op: WBs[literal_unary], typ: Ty) -> WBs[UnaryOpKind]:
        ...

    @staticmethod
    @overload
    def resolve_overloading(op: literal_unary, typ: Ty) -> UnaryOpKind:
        ...

    @staticmethod
    def resolve_overloading(op: literal_unary | WBs[literal_unary], typ: Ty):
        def resolve(op: literal_unary, typ: Ty) -> UnaryOpKind:
            match op, typ:
                case '-', TyInt():
                    return UnaryOpKind.I_NEG
                case ('-' | '-.'), TyFloat():
                    return UnaryOpKind.F_NEG
                case _:
                    raise NotImplementedError(op, typ)

        if isinstance(op, WBs):
            return WBs(resolve(op.val, typ), op.bounds)
        return resolve(op, typ)

    def __init__(self, op: WBs[UnaryOpKind], y: Id, /, *, bounds: Bounds):
        assert isinstance(y, Id)
        assert isinstance(op, WBs) and isinstance(op.val, UnaryOpKind)
        super(Unary, self).__init__(bounds, op.val.typ.ret)
        self.op = op
        self.y = y

    def __str__(self):
        return f"({str(self.op.val)} {self.y})"


class App(KNormal[Ty]):
    __slots__ = 'callee', 'args'

    def __init__(self, f: Id, *args: Id, typ: Ty, bounds: Bounds):
        assert isinstance(f, Id) and all(isinstance(arg, Id) for arg in args)
        assert len(args) >= 1
        super(App, self).__init__(bounds, typ)
        self.callee = f
        self.args = args

    def __str__(self):
        return f"({self.callee} {' '.join(map(str, self.args))})"


class Binary(KNormal[Ty]):
    __slots__ = 'op', 'y1', 'y2'

    @staticmethod
    @overload
    def resolve_overloading(op: WBs[literal_binary], typ: Ty) -> WBs[BinaryOpKind]:
        ...

    @staticmethod
    @overload
    def resolve_overloading(op: literal_binary, typ: Ty) -> BinaryOpKind:
        ...

    @staticmethod
    def resolve_overloading(op: literal_binary | WBs[literal_binary], typ: Ty):
        def resolve(op: literal_binary, typ: Ty) -> 'BinaryOpKind':
            match op, typ:
                case '+', TyInt():
                    return BinaryOpKind.I_ADD
                case '-', TyInt():
                    return BinaryOpKind.I_SUB
                case '*', TyInt():
                    return BinaryOpKind.I_MUL
                case '/', TyInt():
                    return BinaryOpKind.I_DIV
                case ('+' | '+.'), TyFloat():
                    return BinaryOpKind.F_ADD
                case ('-' | '-.'), TyFloat():
                    return BinaryOpKind.F_SUB
                case ('*' | '*.'), TyFloat():
                    return BinaryOpKind.F_MUL
                case ('/.' | '/'), TyFloat():
                    return BinaryOpKind.F_DIV
                case '<', TyInt():
                    return BinaryOpKind.I_LT
                case '<', TyFloat():
                    return BinaryOpKind.F_LT
                case '<=', TyInt():
                    return BinaryOpKind.I_LE
                case '<=', TyFloat():
                    return BinaryOpKind.F_LE
                case '=', TyInt():
                    return BinaryOpKind.I_EQ
                case '=', TyFloat():
                    return BinaryOpKind.F_EQ
                case '=', TyBool():
                    return BinaryOpKind.B_EQ
                case '<>', TyInt():
                    return BinaryOpKind.I_NEQ
                case '<>', TyFloat():
                    return BinaryOpKind.F_NEQ
                case '<>', TyBool():
                    return BinaryOpKind.B_NEQ
                case '>=', TyInt():
                    return BinaryOpKind.I_GE
                case '>=', TyFloat():
                    return BinaryOpKind.F_GE
                case '>', TyInt():
                    return BinaryOpKind.I_GT
                case '>', TyFloat():
                    return BinaryOpKind.F_GT
                case _:
                    raise NotImplementedError()

        if isinstance(op, WBs):
            return WBs(resolve(op.val, typ), op.bounds)
        return resolve(op, typ)

    def __init__(self, op: WBs[BinaryOpKind], y1: Id, y2: Id, *, bounds: Bounds):
        assert isinstance(op, WBs) and isinstance(op.val, BinaryOpKind)
        assert isinstance(y1, Id) and isinstance(y2, Id)
        super(Binary, self).__init__(bounds, op.val.typ.ret)
        self.op = op
        self.y1 = y1
        self.y2 = y2

    def __str__(self):
        return f"({self.y1} {str(self.op.val)} {self.y2})"


class Seq(KNormal[Ty]):
    __slots__ = 'es',

    def __init__(self, *es: KNormal[Ty]):
        assert len(es) >= 2
        assert all(isinstance(e, KNormal) for e in es)
        assert all(e.typ is TyUnit() for e in es[:-1])
        bounds = merge_bounds(*(e.bounds for e in es))
        super(Seq, self).__init__(bounds, es[-1].typ)
        self.es = es

    def __str__(self):
        return f"({'; '.join(map(str, self.es))})"


class Tuple(KNormal[TyTuple]):
    __slots__ = 'ys',

    def __init__(self, *ys: Id, typ: TyTuple, bounds: Bounds):
        """check elems is at least of length 2 at runtime"""
        assert all(isinstance(e, Id) for e in ys)
        assert isinstance(typ, TyTuple) and len(typ.elems) == len(ys)
        super(Tuple, self).__init__(bounds, typ)
        self.ys = ys

    def __str__(self):
        return f"({', '.join(map(str, self.ys))})"


class Put(KNormal[TyUnit]):
    __slots__ = 'array', 'index', 'value'

    def __init__(self, array: Id, index: Id, value: Id, /, *, bounds: Bounds):
        assert isinstance(array, Id) and isinstance(index, Id) and isinstance(value, Id)
        super(Put, self).__init__(bounds, TyUnit())
        self.array, self.index, self.value = array, index, value

    def __str__(self):
        return f"({self.array}.({self.index}) <- {self.value})"


class If(KNormal[Ty]):
    __slots__ = 'cond', 'br_true', 'br_false'

    def __init__(self, cond: Id, branch_true: KNormal[Ty], branch_false: KNormal[Ty], /, *, bounds: Bounds):
        assert isinstance(cond, Id) and isinstance(branch_true, KNormal) and isinstance(branch_false, KNormal)
        assert branch_true.typ == branch_false.typ
        super(If, self).__init__(bounds, branch_true.typ)
        self.cond = cond
        self.br_true = branch_true
        self.br_false = branch_false

    def __str__(self):
        return f"(if {self.cond} then {self.br_true} else {self.br_false})"


class LetBinding(HasBounds):
    __slots__ = 'lhs', 'rhs'

    def __init__(self, lhs: Id, rhs: KNormal[Ty], /, *, bounds: Bounds):
        assert isinstance(lhs, Id) and isinstance(rhs, KNormal)
        super(LetBinding, self).__init__(bounds)
        self.lhs = lhs
        self.rhs = rhs

    def __str__(self):
        if self.lhs.is_tmp:
            return f"let {self.lhs}: {self.rhs.typ} = {self.rhs}"
        return f"let {self.lhs} = {self.rhs}"


class Let(KNormal[T]):
    __slots__ = 'binding', 'expr'

    def __init__(self, binding: LetBinding, expr: KNormal[T], /, *, bounds: Bounds):
        assert isinstance(binding, LetBinding) and isinstance(expr, KNormal)
        super(Let, self).__init__(bounds, expr.typ)
        self.binding = binding
        self.expr = expr

    def __str__(self):
        if self.binding.lhs.is_tmp:
            return f"(let {self.binding.lhs}: {self.binding.rhs.typ} = {self.binding.rhs} in {self.expr})"
        return f"(let {self.binding.lhs} = {self.binding.rhs} in {self.expr})"


class LetTuple(KNormal[T]):
    __slots__ = 'xs', 'ts', 'y', 'e'

    def __init__(self, xs: tuple[Id, ...], ts: tuple[Ty, ...], y: Id, e: KNormal[T], /, *, bounds: Bounds):
        """
        constraints:
        if x_i is LocalId, then x_i.is_definition must be True
        """
        assert isinstance(xs, tuple) and len(xs) >= 2
        assert all(isinstance(x, Id) for x in xs)
        assert all(isinstance(t, Ty) for t in ts)
        assert len(xs) == len(ts)
        assert isinstance(y, Id)
        assert isinstance(e, KNormal)
        super(LetTuple, self).__init__(bounds, e.typ)
        self.xs = xs
        self.ts = ts
        self.y = y
        self.e = e

    def update(self, /, *, e: KNormal[T] | None = None):
        if (e or self.e) is self.e:
            return self
        return LetTuple(self.xs, self.ts, self.y, e or self.e, bounds=self.bounds)

    def __str__(self):
        return f"(let ({', '.join(f'({x}: {t})' for x, t in zip(self.xs, self.ts))}) = {self.y} in {self.e})"


class Function(HasBounds):
    __slots__ = 'funct', 'formal_args', 'body', 'typ'

    def __init__(self, funct: Id, formal_args: tuple[Id, ...], body: KNormal[Ty], /, *,
                 typ: TyFun, bounds: Bounds):
        assert isinstance(formal_args, tuple) and isinstance(typ, TyFun)
        assert all(isinstance(x, Id) for x in formal_args)
        assert len(formal_args) == len(typ.args)
        assert isinstance(body, KNormal) and body.typ == typ.ret
        HasBounds.__init__(self, bounds)
        self.funct = funct
        self.formal_args = formal_args
        self.body = body
        self.typ = typ

    def iter_args(self):
        return zip(self.formal_args, self.typ.args)

    def update(self, /, *, body: KNormal[Ty]):
        if body is self.body: return self
        return Function(self.funct, self.formal_args, body, typ=self.typ, bounds=self.bounds)

    def __str__(self):
        args = ' '.join(f"({a}: {t})" for a, t in self.iter_args())
        return f"let rec {self.funct} {args}: {self.typ.ret} = {self.body}"

    def __repr__(self):
        return f"{self.__class__.__module__}.{self.__class__.__qualname__}({self.funct})"


# class ArrayMake(Function):
#     __slots__ = 'typ', 'size'

#     def __init__(self, name: GlobalId):
#         super(ArrayMake, self).__init__(name, (length, val), Seq(),
#                                         typ=lambda a: TyFun(TyInt(), a, TyArray(a)))
#         self.size = length

#     def __str__(self):
#         return f"make_array {self.size}"

#     def __repr__(self):
#         return f"{self.__class__.__module__}.{self.__class__.__qualname__}({self.size})"


class LetRec(KNormal[Ty]):
    __slots__ = 'f', 'e'

    def __init__(self, func: Function, expr: KNormal[Ty], /, *, bounds: Bounds):
        """
        let rec $name $arg1 ... $argn = $body in $expr
        """
        assert isinstance(func, Function)
        assert isinstance(expr, KNormal)
        assert self is not expr
        super(LetRec, self).__init__(bounds, expr.typ)
        self.f = func
        self.e = expr

    def __str__(self):
        args = ' '.join(f"({a}: {t})" for a, t in self.f.iter_args())
        return f"(let rec {self.f.funct} {args}: {self.f.typ.ret} = {self.f.body} in {self.e})"

    def update(self, /, *, f: Function | None = None, e: KNormal[Ty] | None = None):
        if (f or self.f) is self.f and (e or self.e) is self.e:
            return self
        return LetRec(f or self.f, e or self.e, bounds=self.bounds)


class Module(HasBounds):
    __slots__ = 'items'

    def __init__(self, *items: KNormal[Ty] | LetBinding | Function, bounds: Bounds):
        assert len(items) >= 1
        assert all(isinstance(item, (KNormal, LetBinding, Function)) for item in items)
        super(Module, self).__init__(bounds)
        self.items = items

# class Decl(KNormal):
#     __slots__ = 'binding', 'e'
#
#     def __init__(self, binding: LetBinding, /, *, bounds: Bounds):
#         HasBounds.__init__(self, bounds)
#         self.x = x
#         self.e = e
#
#     def __str__(self):
#         return f"let {self.x} = {self.e}"
#
#
# class DeclRec(KNormal):
#     __slots__ = 'f',
#
#     def __init__(self, f: Function, /, *, bounds: Bounds):
#         assert isinstance(f, Function)
#         HasBounds.__init__(self, bounds)
#         self.f = f
#
#     def __str__(self):
#         args = ' '.join(f"({a}: {t})" for a, t in self.f.iter_args())
#         return f"let rec {self.f.funct} {args}: {self.f.typ.ret} = {self.f.body}"
#
#
# class TopLevel(KNormal):
#     __slots__ = 'decl_or_exprs',
#
#     def __init__(self, *decl_or_exprs: Decl | DeclRec | Expr, bounds: Bounds):
#         assert all(isinstance(e, (Decl, DeclRec, Expr)) for e in decl_or_exprs)
#         assert len(decl_or_exprs) >= 1
#         HasBounds.__init__(self, bounds)
#         self.decl_or_exprs = decl_or_exprs
#
#     def __str__(self):
#         return '\n'.join(map(str, self.decl_or_exprs)) + '\n'
