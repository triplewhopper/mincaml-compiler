from withbounds import WithBounds, merge
from typing import Literal, NewType, Tuple as Tup, TypeVar
from abc import ABC, abstractmethod
import ty0

de_bruijn_level = NewType("de_bruijn_level", int)
binary_operators = {'+', '+.', '-', '-.', '*.', '/.', '<', '<=', '>', '>=', '=', '<>'}
literal_binary = Literal['+', '+.', '-', '-.', '*.', '/.', '<', '<=', '>', '>=', '=', '<>']
unary_operators = ('-', '-.')
literal_unary = Literal['-', '-.']

T = TypeVar("T")


class Node:
    __slots__ = ["_bounds"]

    def __init__(self, bounds: tuple[int, int]):
        assert isinstance(bounds, tuple) and len(bounds) == 2
        assert isinstance(bounds[0], int) and isinstance(bounds[1], int)
        assert bounds[0] < bounds[1]
        self._bounds = bounds

    @property
    def bounds(self) -> tuple[int, int]:
        return self._bounds

    def accept(self, visitor: 'NodeVisitor'):
        return visitor.visit(self)


class Lit(Node):
    __slots__ = ["_val"]
    __match_args__ = ('val',)

    def __init__(self, val: WithBounds[int | float | bool | Literal['()']]):
        super(Lit, self).__init__(val.bounds)
        self._val = val

    @property
    def val(self) -> int | float | bool | Literal['()']:
        return self._val.val

    def get_val_with_bounds(self) -> WithBounds[int | float | bool | Literal['()']]:
        return self._val

    def __str__(self):
        if self.val is True:
            return "true"
        if self.val is False:
            return "false"
        return str(self.val)


class Var(Node):
    """
    for Array.make and Array.create,
    do name mangling by appending a suffix indicating the source location
    """
    __slots__ = ["_name", "_tyvar", "_is_ext"]
    __match_args__ = ('name',)

    def __init__(self, name: WithBounds[str]):
        assert isinstance(name, WithBounds) and isinstance(name.val, str)
        super(Var, self).__init__(name.bounds)
        # if name.val in ('Array.make', 'Array.create'):
        #     # TODO: fix this ugly hack
        #     # name = WithBounds(name.val + f"_at_{name.bounds[0]}_{name.bounds[1]}", name.bounds)
        #     self._is_array_make = True
        # else:
        #     self._is_array_make = False
        self._name = name
        self._tyvar = None
        self._is_ext = None

    @property
    def name(self) -> WithBounds[str]:
        return self._name

    @property
    def tyvar(self) -> ty0.TyVar:
        assert self._tyvar is not None
        return self._tyvar

    @tyvar.setter
    def tyvar(self, tyvar: ty0.TyVar):
        assert self._tyvar is None
        self._tyvar = tyvar

    @property
    def is_ext(self) -> bool:
        assert self._is_ext is not None
        return self._is_ext

    @is_ext.setter
    def is_ext(self, is_ext: bool):
        assert self._is_ext is None
        assert isinstance(is_ext, bool)
        self._is_ext = is_ext

    # def is_array_make(self) -> bool:
    #     return self._is_array_make

    def __str__(self):
        return str(self._name.val)


class Get(Node):
    """
    e1.(e2)
    """
    __slots__ = ["_e1", "_e2"]
    __match_args__ = ('e1', 'e2')

    def __init__(self, e1: Node, e2: Node):
        assert isinstance(e1, Node) and isinstance(e2, Node)
        assert e1.bounds[1] <= e2.bounds[0]
        super(Get, self).__init__((e1.bounds[0], e2.bounds[1]))
        self._e1 = e1
        self._e2 = e2

    @property
    def e1(self) -> Node:
        return self._e1

    @property
    def e2(self) -> Node:
        return self._e2

    def __str__(self):
        return f"{self.e1}.({self.e2})"


class Unary(Node):
    __slots__ = ["_op", "_e"]
    __match_args__ = ('op', 'e')

    def __init__(self, op: WithBounds[literal_unary], e: Node):
        assert isinstance(op, WithBounds) and op.val in unary_operators
        assert isinstance(e, Node)
        assert op.bounds[1] <= e.bounds[0]
        super(Unary, self).__init__((op.bounds[0], e.bounds[1]))
        self._op = op
        self._e = e

    @property
    def op(self) -> WithBounds[literal_unary]:
        return self._op

    @property
    def e(self) -> Node:
        return self._e

    def __str__(self):
        return f"({self.op.val} {self.e})"


class App(Node):
    __slots__ = ["_callee", "_args"]
    __match_args__ = ('callee', 'args')

    def __init__(self, callee: Node, *args: Node):
        assert isinstance(callee, Node)
        assert len(args) >= 1
        assert all(isinstance(arg, Node) for arg in args)
        assert callee.bounds[1] <= args[0].bounds[0]
        for i in range(len(args) - 1):
            assert args[i].bounds[1] <= args[i + 1].bounds[0]
        super(App, self).__init__((callee.bounds[0], args[-1].bounds[1]))
        self._callee = callee
        self._args = args

    @property
    def callee(self) -> Node:
        return self._callee

    @property
    def args(self) -> tuple[Node, ...]:
        return self._args

    def __str__(self):
        return f"({self.callee} {' '.join(map(str, self.args))})"


class Binary(Node):
    __slots__ = ["_op", "_e1", "_e2"]
    __match_args__ = ('op', 'e1', 'e2')

    def __init__(self, op: WithBounds[literal_binary], e1: Node, e2: Node):
        assert isinstance(op, WithBounds)
        assert op.val in binary_operators
        assert isinstance(e1, Node) and isinstance(e2, Node)
        assert e1.bounds[1] <= op.bounds[0]
        assert op.bounds[1] <= e2.bounds[0]
        super(Binary, self).__init__((e1.bounds[0], e2.bounds[1]))
        self._op = op
        self._e1 = e1
        self._e2 = e2

    @property
    def op(self) -> WithBounds[literal_binary]:
        return self._op

    @property
    def e1(self) -> Node:
        return self._e1

    @property
    def e2(self) -> Node:
        return self._e2

    def __str__(self):
        return f"({self.e1} {self.op.val} {self.e2})"


class Semi(Node):
    __slots__ = ["_es"]
    __match_args__ = ('es',)

    def __init__(self, es: Tup[Node, ...]):
        assert len(es) >= 2
        assert all(isinstance(e, Node) for e in es)
        assert all(es[i].bounds[1] <= es[i + 1].bounds[0] for i in range(len(es) - 1))
        super(Semi, self).__init__((es[0].bounds[0], es[-1].bounds[1]))
        self._es = es

    @property
    def es(self) -> Tup[Node, ...]:
        return self._es

    def __str__(self):
        return f"({'; '.join(map(str, self.es))})"


class Tuple(Node):
    __match_args__ = ('es',)

    def __init__(self, es: Tup[Node, ...]):
        assert len(es) >= 2
        assert all(isinstance(e, Node) for e in es)
        super(Tuple, self).__init__((es[0].bounds[0], es[-1].bounds[1]))
        self._es = es

    @property
    def es(self) -> tuple[Node, ...]:
        return self._es

    def __str__(self):
        return f"({', '.join(map(str, self.es))})"


class Node3(Node):
    __slots__ = ['_e1', '_e2', '_e3']
    __match_args__ = ('e1', 'e2', 'e3')

    def __init__(self, e1: Node, e2: Node, e3: Node, bounds: tuple[int, int] = None):
        assert isinstance(e1, Node) and isinstance(e2, Node) and isinstance(e3, Node)
        assert e1.bounds[1] <= e2.bounds[0] and e2.bounds[1] <= e3.bounds[0]
        super(Node3, self).__init__(bounds or (e1.bounds[0], e3.bounds[1]))
        self._e1, self._e2, self._e3 = e1, e2, e3

    @property
    def e1(self) -> Node:
        return self._e1

    @property
    def e2(self) -> Node:
        return self._e2

    @property
    def e3(self) -> Node:
        return self._e3

    @abstractmethod
    def __str__(self):
        ...


class Put(Node3):
    """
    e1.(e2) <- e3
    """
    __slots__ = []

    def __str__(self):
        return f"({self.e1}.({self.e2}) <- {self.e3})"


class If(Node3):
    __slots__ = []

    def __init__(self, if_tok: WithBounds[Literal['if']], e1: Node, e2: Node, e3: Node):
        assert if_tok.bounds[1] <= min(e1.bounds[0], e2.bounds[0], e3.bounds[0])
        super(If, self).__init__(e1, e2, e3, (if_tok.bounds[0], max(e2.bounds[1], e3.bounds[1])))

    def __str__(self):
        return f"(if {self.e1} then {self.e2} else {self.e3})"


class Let(Node):
    __slots__ = ['_x', '_e1', '_e2']
    __match_args__ = ('x', 'e1', 'e2')

    def __init__(self, let_tok: WithBounds[Literal['let']], x: WithBounds[str], e1: Node, e2: Node):
        assert let_tok.bounds[1] <= x.bounds[0]
        assert x.bounds[1] <= e1.bounds[0]
        assert e1.bounds[1] <= e2.bounds[0]
        super(Let, self).__init__((let_tok.bounds[0], e2.bounds[1]))
        self._x = x
        self._e1 = e1
        self._e2 = e2

    @property
    def x(self) -> WithBounds[str]:
        return self._x

    @property
    def e1(self) -> Node:
        return self._e1

    @property
    def e2(self) -> Node:
        return self._e2

    @property
    def bounds(self):
        return self._bounds

    def __str__(self):
        return f"(let {self.x} = {self.e1} in {self.e2})"


class Function:
    __slots__ = ['_funct', '_formal_args', '_formal_args_val', '_body', '_bounds']
    __match_args__ = ('funct', 'formal_args', 'body')

    def __init__(self, let_tok: WithBounds[Literal['let']], rec_tok: WithBounds[Literal['rec']],
                 funct: WithBounds[str], formal_args: list[WithBounds[str]], body: Node):
        assert len(formal_args) >= 1
        assert funct.val != '_'
        self._funct = funct
        self._formal_args = tuple(formal_args)
        self._formal_args_val = tuple(x.val for x in formal_args)
        self._body = body
        assert let_tok.bounds[1] <= rec_tok.bounds[0]
        assert rec_tok.bounds[1] <= funct.bounds[0]
        assert funct.bounds[1] <= formal_args[0].bounds[0]
        for i in range(len(formal_args) - 1):
            assert formal_args[i].bounds[1] <= formal_args[i + 1].bounds[0]
        assert formal_args[-1].bounds[1] <= body.bounds[0]
        self._bounds = let_tok.bounds[0], body.bounds[1]

    @property
    def funct(self) -> WithBounds[str]:
        return self._funct

    @property
    def formal_args(self) -> tuple[WithBounds[str], ...]:
        return self._formal_args

    @property
    def body(self) -> Node:
        return self._body

    @property
    def bounds(self):
        return self._bounds


class LetRec(Node):
    __slots__ = ['_f', '_e']

    def __init__(self, f: Function, e: Node):
        assert isinstance(f, Function) and isinstance(e, Node)
        assert f.bounds[1] <= e.bounds[0]
        super(LetRec, self).__init__((f.bounds[0], e.bounds[1]))
        self._f = f
        self._e = e

    @property
    def f(self) -> Function:
        return self._f

    @property
    def e(self) -> Node:
        return self._e

    def __str__(self):
        return f"(let rec {self._f.funct.val} {' '.join(x.val for x in self._f.formal_args)} = {self._f.body} in\n{self._e})"


class LetTuple(Node):
    __slots__ = ['_xs', '_e1', '_e2']
    __match_args__ = ('xs', 'e1', 'e2')

    def __init__(self, let_tok: WithBounds[Literal['let']], xs: list[WithBounds[str]], e1: Node, e2: Node):
        assert len(xs) >= 1
        assert let_tok.bounds[1] <= xs[0].bounds[0]
        for i in range(len(xs) - 1):
            assert xs[i].bounds[1] <= xs[i + 1].bounds[0]
        assert xs[-1].bounds[1] <= e1.bounds[0]
        assert e1.bounds[1] <= e2.bounds[0]

        super(LetTuple, self).__init__((let_tok.bounds[0], e2.bounds[1]))
        self._xs = tuple(xs)
        self._e1 = e1
        self._e2 = e2

    @property
    def xs(self) -> tuple[WithBounds[str], ...]:
        return self._xs

    @property
    def e1(self) -> Node:
        return self._e1

    @property
    def e2(self) -> Node:
        return self._e2

    def __str__(self):
        return f"(let ({', '.join(x.val for x in self._xs)}) = {self._e1} in {self._e2})"


class NodeVisitor(ABC):
    def visit(self, node: Node):
        return getattr(self, f"visit_{type(node).__name__}")(node)

    @abstractmethod
    def visit_Lit(self, node: Lit):
        ...

    @abstractmethod
    def visit_Var(self, node: Var):
        ...

    @abstractmethod
    def visit_Get(self, node: Get):
        ...

    @abstractmethod
    def visit_Unary(self, node: Unary):
        ...

    @abstractmethod
    def visit_Semi(self, node: Semi):
        ...

    @abstractmethod
    def visit_App(self, node: App):
        ...

    @abstractmethod
    def visit_Binary(self, node: Binary):
        ...

    @abstractmethod
    def visit_Tuple(self, node: Tuple):
        ...

    @abstractmethod
    def visit_Put(self, node: Put):
        ...

    @abstractmethod
    def visit_If(self, node: If):
        ...

    @abstractmethod
    def visit_Let(self, node: Let):
        ...

    @abstractmethod
    def visit_LetRec(self, node: LetRec):
        ...

    @abstractmethod
    def visit_LetTuple(self, node: LetTuple):
        ...
