# from abc import ABC, abstractmethod
# from typing import Generic, TypeVar
# from .language import Exp, Lit, Var, Ext, Get, Unary, AppCls, AppDir, Binary, Seq, Tuple, Put, If, Let, LetTuple, \
#     MakeCls

# T = TypeVar("T")


# class ExpVisitor(ABC, Generic[T]):
#     __slots__ = ()

#     @abstractmethod
#     def visit_Lit(self, node: Lit, /):
#         ...

#     @abstractmethod
#     def visit_Var(self, node: Var, /):
#         ...

#     @abstractmethod
#     def visit_Ext(self, node: Ext, /):
#         ...

#     @abstractmethod
#     def visit_Get(self, node: Get, /):
#         ...

#     @abstractmethod
#     def visit_Unary(self, node: Unary, /):
#         ...

#     @abstractmethod
#     def visit_AppCls(self, node: AppCls, /):
#         ...

#     @abstractmethod
#     def visit_AppDir(self, node: AppDir, /):
#         ...

#     @abstractmethod
#     def visit_Binary(self, node: Binary, /):
#         ...

#     @abstractmethod
#     def visit_Seq(self, node: Seq, /):
#         ...

#     @abstractmethod
#     def visit_Tuple(self, node: Tuple, /):
#         ...

#     @abstractmethod
#     def visit_Put(self, node: Put, /):
#         ...

#     @abstractmethod
#     def visit_If(self, node: If, /):
#         ...

#     @abstractmethod
#     def visit_Let(self, node: Let, /):
#         ...

#     @abstractmethod
#     def visit_LetTuple(self, node: LetTuple, /):
#         ...

#     @abstractmethod
#     def visit_MakeCls(self, node: MakeCls, /):
#         ...

#     def visit(self, node: Exp, /) -> T:
#         return getattr(self, f"visit_{node.__class__.__name__}")(node)


