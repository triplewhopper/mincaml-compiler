from withbounds import WithBounds, is_disjoint_increasing, WithBoundsLit, X
from bounds import Bounds, HasBounds
from opkinds import literal_unary, literal_binary, unary_operators, binary_operators
from abc import abstractmethod
from typing import Literal
import asyncio
import ty0


class Node(HasBounds):
    __slots__ = ()


class Expr(Node):
    __slots__ = ()


class Lit(Expr):
    __slots__ = '_lit',

    def __init__(self, val: WithBoundsLit[X]):
        super(Lit, self).__init__(val.bounds)
        self._lit = val

    @property
    def lit(self):
        return self._lit

    def __str__(self):
        if self._lit.val is True:
            return "true"
        if self._lit.val is False:
            return "false"
        return str(self._lit.val)


class Var(Expr):
    __slots__ = 'name', 'ty0'

    def __init__(self, name: WithBounds[str]):
        assert isinstance(name, WithBounds) and isinstance(name.val, str)
        super(Var, self).__init__(name.bounds)
        self.name = name
        self.ty0 = asyncio.Future[ty0.Ty0]()

    def __str__(self):
        return self.name.val


# class E1:

#     def __set__(self, instance: Expr, value: Expr):
#         raise AttributeError('readonly')

#     def __get__(self, instance: Expr, owner: type[Expr]):
#         return instance._e1


# class E2:
#     def __set__(self, instance, value):
#         assert isinstance(value, Expr)
#         instance._e2 = value

#     def __get__(self, instance, owner):
#         return instance._e2


# class E3:
#     def __set__(self, instance, value):
#         assert isinstance(value, Expr)
#         instance.__e3 = value

#     def __get__(self, instance, owner):
#         return instance.__e3


class _HasE1:
    __slots__ = ()

    def __init__(self, e1: Expr):
        assert isinstance(e1, Expr)
        self._e1 = e1

    @property
    def e1(self) -> Expr:
        return self._e1


class _HasE2:
    __slots__ = ()

    def __init__(self, e2: Expr):
        assert isinstance(e2, Expr)
        self._e2 = e2

    @property
    def e2(self) -> Expr:
        return self._e2


class _HasE:
    __slots__ = ()

    def __init__(self, e: Expr):
        assert isinstance(e, Expr)
        self._e = e

    @property
    def e(self) -> Expr:
        return self._e


class Get(Expr, _HasE1, _HasE2):
    __slots__ = '_e1', '_e2'

    def __init__(self, e1: Expr, lparen: WithBounds[Literal['(']], e2: Expr, rparen: WithBounds[Literal[')']]):
        assert isinstance(lparen, WithBounds) and lparen.val == '('
        assert isinstance(rparen, WithBounds) and rparen.val == ')'
        assert is_disjoint_increasing(e1.bounds, lparen.bounds, e2.bounds, rparen.bounds)
        Expr.__init__(self, e1.bounds | rparen.bounds)
        self._e1 = e1
        self._e2 = e2

    def __str__(self):
        return f"{self.e1}.({self.e2})"


class Unary(Expr, _HasE):
    __slots__ = 'op', '_e'

    def __init__(self, op: WithBounds[literal_unary], e: Expr):
        assert isinstance(op, WithBounds) and op.val in unary_operators
        _HasE.__init__(self, e)
        assert op.bounds < e.bounds
        Expr.__init__(self, op.bounds | e.bounds)

        self.op = op

    def __str__(self):
        return f"({self.op.val} {self.e})"


class App(Expr):

    def __init__(self, callee: Expr, *args: Expr):
        assert isinstance(callee, Expr)
        assert 1 <= len(args) and all(isinstance(arg, Expr) for arg in args)
        assert is_disjoint_increasing(callee.bounds, *(arg.bounds for arg in args))
        super(App, self).__init__(callee.bounds | args[-1].bounds)
        self.callee, self.args = callee, args

    def __str__(self):
        return f"({self.callee} {' '.join(map(str, self.args))})"


class Binary(Expr, _HasE1, _HasE2):
    __slots__ = 'op', '_e1', '_e2'

    def __init__(self, op: WithBounds[literal_binary], e1: Expr, e2: Expr):
        assert isinstance(op, WithBounds)
        assert op.val in binary_operators
        _HasE1.__init__(self, e1)
        _HasE2.__init__(self, e2)
        assert e1.bounds < op.bounds < e2.bounds
        super(Binary, self).__init__(e1.bounds | e2.bounds)
        self.op = op

    def __str__(self):
        return f"({self.e1} {self.op.val} {self.e2})"


class _HasEs:
    __slots__ = ()

    def __init__(self, es: tuple[Expr, ...]):
        assert all(isinstance(e, Expr) for e in es)
        self._es = es

    @property
    def es(self) -> tuple[Expr, ...]:
        return self._es


class Semi(Expr, _HasEs):
    __slots__ = '_es'

    def __init__(self, es: tuple[Expr, ...]):
        _HasEs.__init__(self, es)
        assert len(es) >= 2
        assert is_disjoint_increasing(*(e.bounds for e in es))
        Expr.__init__(self, es[0].bounds | es[-1].bounds)

    def __str__(self):
        return f"({'; '.join(map(str, self.es))})"


class Tuple(Expr, _HasEs):
    __slots__ = '_es'

    def __init__(self, es: tuple[Expr, ...]):
        _HasEs.__init__(self, es)
        assert len(es) >= 2
        assert is_disjoint_increasing(*(e.bounds for e in es))
        super(Tuple, self).__init__(es[0].bounds | es[-1].bounds)

    def __str__(self):
        return f"({', '.join(map(str, self.es))})"


# class E3:
#     def __set__(self, instance, value):
#         assert isinstance(value, Expr)
#         instance._e3 = value
#
#     def __get__(self, instance, owner):
#         return instance._e3


class _HasE3:
    __slots__ = ()

    def __init__(self, e3: Expr):
        assert isinstance(e3, Expr)
        self._e3 = e3

    @property
    def e3(self) -> Expr:
        return self._e3


class Expr3(Expr, _HasE1, _HasE2, _HasE3):
    __slots__ = '_e1', '_e2', '_e3'

    def __init__(self, e1: Expr, e2: Expr, e3: Expr, bounds: Bounds | None = None):
        _HasE1.__init__(self, e1)
        _HasE2.__init__(self, e2)
        _HasE3.__init__(self, e3)
        assert e1.bounds < e2.bounds < e3.bounds
        super(Expr3, self).__init__(bounds or (e1.bounds | e3.bounds))

    @abstractmethod
    def __str__(self) -> str:
        ...


class Put(Expr3):
    """
    e1.(e2) <- e3
    """
    __slots__ = ()

    def __str__(self):
        return f"({self.e1}.({self.e2}) <- {self.e3})"


class If(Expr3):
    __slots__ = ()

    def __init__(self, if_tok: WithBounds[Literal['if']], e1: Expr, e2: Expr, e3: Expr):
        assert if_tok.bounds < e1.bounds and if_tok.bounds < e2.bounds and if_tok.bounds < e3.bounds
        super(If, self).__init__(e1, e2, e3, if_tok.bounds | e2.bounds | e3.bounds)

    def __str__(self):
        return f"(if {self.e1} then {self.e2} else {self.e3})"


class LetBinding(HasBounds, _HasE1):
    __slots__ = 'var', '_e1'

    def __init__(self, let_tok: WithBounds[Literal['let']], var: WithBounds[str], e1: Expr):
        _HasE1.__init__(self, e1)
        assert isinstance(let_tok, WithBounds) and let_tok.val == 'let'
        assert let_tok.bounds < var.bounds < e1.bounds
        HasBounds.__init__(self, let_tok.bounds | var.bounds | e1.bounds)
        assert isinstance(var, WithBounds) and isinstance(var.val, str)
        self.var = var


class Let(Expr, _HasE2):
    __slots__ = 'binding', '_e2'

    def __init__(self, let_binding: LetBinding, e2: Expr):
        _HasE2.__init__(self, e2)
        assert let_binding.bounds < e2.bounds
        super(Let, self).__init__(let_binding.bounds | e2.bounds)
        self.binding = let_binding

    def __str__(self):
        return f"(let {self.binding.var.val} = {self.binding.e1} in {self.e2})"


class Function(_HasE1):
    __slots__ = 'funct', 'formal_args', '_e1', 'bounds'

    def __init__(self, let_tok: WithBounds[Literal['let']], rec_tok: WithBounds[Literal['rec']],
                 funct: WithBounds[str], formal_args: list[WithBounds[str]], body: Expr):
        assert len(formal_args) >= 1
        assert funct.val != '_'
        assert is_disjoint_increasing(
            let_tok.bounds, rec_tok.bounds, funct.bounds, *(x.bounds for x in formal_args), body.bounds)
        self.funct = funct
        self.formal_args = tuple(formal_args)
        _HasE1.__init__(self, body)
        self.bounds = let_tok.bounds | body.bounds


class LetRec(Expr, _HasE2):
    __slots__ = 'f', '_e2'

    def __init__(self, f: Function, e2: Expr):
        _HasE2.__init__(self, e2)
        assert isinstance(f, Function)
        assert f.bounds < e2.bounds
        super(LetRec, self).__init__(f.bounds | e2.bounds)
        self.f = f

    def __str__(self):
        return f"(let rec {self.f.funct.val} {' '.join(x.val for x in self.f.formal_args)} = {self.f.e1} in\n{self.e2})"


class LetTuple(Expr, _HasE1, _HasE2):
    __slots__ = 'xs', '_e1', '_e2'

    def __init__(self, let_tok: WithBounds[Literal['let']], xs: list[WithBounds[str]], e1: Expr, e2: Expr):
        _HasE1.__init__(self, e1)
        _HasE2.__init__(self, e2)
        assert len(xs) >= 1
        assert is_disjoint_increasing(let_tok.bounds, *(x.bounds for x in xs), e1.bounds, e2.bounds)
        super(LetTuple, self).__init__(let_tok.bounds | e2.bounds)
        self.xs = tuple(xs)

    def __str__(self):
        return f"(let ({', '.join(x.val for x in self.xs)}) = {self.e1} in {self.e2})"


class Decl(Node):
    __slots__ = 'binding'

    def __init__(self, binding: LetBinding):
        assert isinstance(binding, LetBinding)
        super(Decl, self).__init__(binding.bounds)
        self.binding = binding

    def __str__(self):
        return f"let {self.binding.var.val} = {self.binding.e1}"


class DeclRec(Node):
    __slots__ = 'f',

    def __init__(self, f: Function):
        assert isinstance(f, Function)
        super(DeclRec, self).__init__(f.bounds)
        self.f = f

    def __str__(self):
        return f"let rec {self.f.funct.val} {' '.join(x.val for x in self.f.formal_args)} = {self.f.e1}"


class TopLevel(Node):
    __slots__ = 'decl_or_exprs',

    def __init__(self, *args: Decl | DeclRec | Expr):
        assert all(isinstance(arg, (Decl, DeclRec, Expr)) for arg in args)
        assert is_disjoint_increasing(*(arg.bounds for arg in args))
        super(TopLevel, self).__init__(args[0].bounds | args[-1].bounds)
        self.decl_or_exprs = args
