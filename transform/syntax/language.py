from metadata import DIVariable, DILocation
import asyncio
from ty0 import Ty0
from id import Id
from dataclasses import dataclass, field
from typing import Literal


class Node:
    __slots__ = ()

    @property
    def location(self) -> DILocation:
        match self:
            case Lit() | Unary() | Binary():
                return self.metadata
            case Var():
                return self.metadata.loc
            case Get(e1=e) | App(callee=e) | Semi(es=[e, *_]) | \
                 Tuple(es=[e, *_]) | Put(e1=e) | If(e1=e) | \
                 Let(binding=LetBinding(var=e)) | LetRec(f=Function(funct=e)) | LetTuple(xs=[e, *_]):
                return e.location
            case LetBinding(var=e) | Function(funct=e):
                return e.location
            case TopLevel(decl_or_exprs=[e, *_]):
                return e.location
            case _:
                raise NotImplementedError(self)


class Expr(Node):
    __slots__ = ()


@dataclass
class Lit(Expr):
    metadata: DILocation


@dataclass
class LitU(Lit):
    lit: Literal['()'] = field(default='()', init=False)

    def __str__(self):
        return "()"


@dataclass
class LitI(Lit):
    lit: int

    def __str__(self):
        return 'true' if self.lit else 'false'


@dataclass
class LitB(Lit):
    lit: bool

    def __str__(self):
        return str(self.lit)


@dataclass
class LitF(Lit):
    lit: float

    def __str__(self):
        return str(self.lit)


@dataclass
class Var(Expr):
    name: Id
    metadata: DIVariable
    ty0: asyncio.Future[Ty0] = field(default_factory=asyncio.Future[Ty0])

    def __str__(self):
        return self.name.__str__()


@dataclass
class Get(Expr):
    e1: Expr
    e2: Expr

    def __str__(self):
        return f"{self.e1}.({self.e2})"


@dataclass
class Unary(Expr):
    metadata: DILocation
    op: str
    e: Expr

    def __str__(self):
        return f"({self.op} {self.e})"


@dataclass
class App(Expr):
    callee: Expr
    args: tuple[Expr, ...]

    def __str__(self):
        return f"({self.callee} {' '.join(map(str, self.args))})"


@dataclass
class Binary(Expr):
    metadata: DILocation
    op: str
    e1: Expr
    e2: Expr

    def __str__(self):
        return f"({self.e1} {self.op} {self.e2})"


@dataclass
class Semi(Expr):
    es: tuple[Expr, ...]

    def __post_init__(self):
        assert len(self.es) >= 2

    def __str__(self):
        return f"({'; '.join(map(str, self.es))})"


@dataclass
class Tuple(Expr):
    es: tuple[Expr, ...]

    def __post_init__(self):
        assert len(self.es) >= 2

    def __str__(self):
        return f"({', '.join(map(str, self.es))})"


@dataclass
class Put(Expr):
    e1: Expr
    e2: Expr
    e3: Expr

    def __str__(self):
        return f"({self.e1}.({self.e2}) <- {self.e3})"


@dataclass
class If(Expr):
    e1: Expr
    e2: Expr
    e3: Expr

    def __str__(self):
        return f"(if {self.e1} then {self.e2} else {self.e3})"


@dataclass
class LetBinding(Node):
    var: Var
    e1: Expr


@dataclass
class Let(Expr):
    binding: LetBinding
    e2: Expr

    def __str__(self):
        return f"(let {self.binding.var} = {self.binding.e1} in {self.e2})"


@dataclass
class Function(Node):
    funct: Var
    formal_args: tuple[Var, ...]
    e1: Expr

    def __post_init__(self):
        assert len(self.formal_args) >= 1
        assert self.funct.name != '_'


@dataclass
class LetRec(Expr):
    f: Function
    e2: Expr

    def __str__(self):
        return f"(let rec {self.f.funct} {' '.join(str(x) for x in self.f.formal_args)} = {self.f.e1} in\n{self.e2})"


@dataclass
class LetTuple(Expr):
    xs: tuple[Var, ...]
    e1: Expr
    e2: Expr

    def __post_init__(self):
        assert len(self.xs) >= 2

    def __str__(self):
        return f"(let ({', '.join(str(x) for x in self.xs)}) = {self.e1} in {self.e2})"


@dataclass
class Decl(Node):
    binding: LetBinding

    def __str__(self):
        return f"let {self.binding.var} = {self.binding.e1}"


@dataclass
class DeclRec(Node):
    f: Function

    def __str__(self):
        return f"let rec {self.f.funct} {' '.join(map(str, self.f.formal_args))} = {self.f.e1}"


@dataclass
class TopLevel(Node):
    decl_or_exprs: tuple[Decl | DeclRec | Expr, ...]
