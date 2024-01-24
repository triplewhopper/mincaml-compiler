from abc import ABC, abstractmethod
from typing import Generic, TypeVar
from .language import Expr, Lit, Var, Get, Unary, Semi, App, Binary, Tuple, Put, If, Let, LetRec, LetTuple

T = TypeVar("T")


class ExprVisitor(ABC, Generic[T]):
    def visit(self, node: Expr) -> T:
        return getattr(self, f"visit_{type(node).__name__}")(node)

    @abstractmethod
    def visit_Lit(self, node: Lit) -> T:
        ...

    @abstractmethod
    def visit_Var(self, node: Var) -> T:
        ...

    @abstractmethod
    def visit_Get(self, node: Get) -> T:
        ...

    @abstractmethod
    def visit_Unary(self, node: Unary) -> T:
        ...

    @abstractmethod
    def visit_Semi(self, node: Semi) -> T:
        ...

    @abstractmethod
    def visit_App(self, node: App) -> T:
        ...

    @abstractmethod
    def visit_Binary(self, node: Binary) -> T:
        ...

    @abstractmethod
    def visit_Tuple(self, node: Tuple) -> T:
        ...

    @abstractmethod
    def visit_Put(self, node: Put) -> T:
        ...

    @abstractmethod
    def visit_If(self, node: If) -> T:
        ...

    @abstractmethod
    def visit_Let(self, node: Let) -> T:
        ...

    @abstractmethod
    def visit_LetRec(self, node: LetRec) -> T:
        ...

    @abstractmethod
    def visit_LetTuple(self, node: LetTuple) -> T:
        ...
