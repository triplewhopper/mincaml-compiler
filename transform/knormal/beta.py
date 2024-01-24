# import dataclasses

# from .language import Var, Ext, Get, Unary, App, Binary, Seq, Tuple, Put, If, Let, LetTuple, LetRec, Function, \
#     KNormal, LetBinding, Module
# from id import Id, LocalId, GlobalId, TmpId
# from ty import Ty, TyTuple, TyFun, TyArray
# from typing import ChainMap, overload
# from .. import bind_logger
# import logging

# get_adapter = bind_logger(logger=logging.getLogger(__name__))

# #
# # def beta(m: Module) -> Module:
# #     items = []
# #     b = Beta()
# #     for item in m.items:
# #         if isinstance(item, Function):
# #             items.append(item.update(body=b.visit(item.body)))
# #         elif isinstance(item, LetBinding):
# #             items.append(


# class Beta:
#     def __init__(self):
#         # self._ty_env = ChainMap[Id, Ty]()
#         self._fa: dict[Id, Id] = {}

#     def visit(self, node: KNormal) -> KNormal:
#         res = super().visit(node)
#         assert res.typ == node.typ
#         assert (res.bounds.lineno, res.bounds.colno) >= (node.bounds.lineno, node.bounds.colno)
#         assert (res.bounds.end_lineno, res.bounds.end_colno) == (node.bounds.end_lineno, node.bounds.end_colno)
#         return res

#     def _find(self, x: Id, /) -> Id:
#         if x in self._fa:
#             self._fa[x] = f = self._find(self._fa[x])
#             return f
#         return x

#     def visit_Var(self, node: Var) -> Var | Ext:
#         name = self._find(node.name)
#         if name is node.name:
#             return node
#         if isinstance(name, GlobalId):
#             typ = node.typ
#             assert isinstance(typ, (TyFun, TyTuple, TyArray))
#             return Ext(name.new_usage(node.bounds), typ=typ)
#         assert isinstance(name, LocalId)
#         return Var(name.new_usage(node.bounds), typ=node.typ)

#     def visit_Ext(self, node: Ext) -> Ext:
#         return node

#     def visit_Get(self, node: Get) -> Get:
#         array = self._find(node.array)
#         index = self._find(node.index)
#         if array is node.array and index is node.index:
#             return node
#         assert isinstance(index, (LocalId, TmpId))
#         return Get(array, index, typ=node.typ, bounds=node.bounds)

#     def visit_Unary(self, node: Unary) -> Unary:
#         y = self._find(node.y)
#         if y is node.y:
#             return node
#         assert isinstance(y, (LocalId, TmpId))
#         return Unary(node.op, y, bounds=node.bounds)

#     def visit_App(self, node: App) -> App:
#         callee = self._find(node.callee)
#         args = [self._find(a) for a in node.args]
#         if callee is node.callee and all(a is b for a, b in zip(args, node.args)):
#             return node
#         return App(callee, *args, typ=node.typ, bounds=node.bounds)

#     def visit_Binary(self, node: Binary) -> Binary:
#         y1 = self._find(node.y1)
#         y2 = self._find(node.y2)
#         if y1 is node.y1 and y2 is node.y2:
#             return node
#         return Binary(node.op, y1, y2, bounds=node.bounds)

#     def visit_Seq(self, node: Seq) -> Seq:
#         es = [self.visit(e) for e in node.es]
#         if all(e is node.es[i] for i, e in enumerate(es)):
#             return node
#         return Seq(*es)

#     def visit_Tuple(self, node: Tuple) -> Tuple:
#         yys = [self._find(y) for y in node.ys]
#         if all(yy is y for yy, y in zip(yys, node.ys)):
#             return node
#         return Tuple(*yys, typ=node.typ, bounds=node.bounds)

#     def visit_Put(self, node: Put) -> Put:
#         array = self._find(node.array)
#         index = self._find(node.index)
#         value = self._find(node.value)
#         if array is node.array and index is node.index and value is node.value:
#             return node
#         return Put(array, index, value, bounds=node.bounds)

#     def visit_If(self, node: If) -> If:
#         cond = self._find(node.cond)
#         t = self.visit(node.br_true)
#         f = self.visit(node.br_false)
#         if cond is node.cond and t is node.br_true and f is node.br_false:
#             return node
#         return If(cond, t, f, bounds=node.bounds)

#     # def visit_LetBinding(self, b: LetBinding):
#     #     rhs = self.visit(b.rhs)
#     #     assert b.lhs not in self._fa
#     #     if isinstance(rhs, (Var, Ext)):
#     #         f = self._find(rhs.name)
#     #         self._fa[b.lhs] = f
#     #         with get_adapter(bounds=b.lhs.bounds) as adapter:
#     #             adapter.info(f"beta-reducing {b.lhs} to {f}")
#     #         return rhs
#     #     return rhs
#     #
#     # def visit_Let(self, node: Let) -> KNormal:
#     #     rhs = self.visit(node.binding.rhs)
#     #     assert node.lhs not in self._fa
#     #     if isinstance(rhs, (Var, Ext)):
#     #         f = self._find(rhs.name)
#     #         self._fa[node.lhs] = f
#     #         with get_adapter(bounds=node.lhs.bounds) as adapter:
#     #             adapter.info(f"beta-reducing {node.lhs} to {f}")
#     #         expr = self.visit(node.expr)
#     #         del self._fa[node.lhs]
#     #         return expr
#     #
#     #     expr = self.visit(node.expr)
#     #     if rhs is node.binding.rhs and expr is node.expr: return node
#     #     return Let(LetBinding(node.binding.lhs, rhs, bounds=node.binding.bounds), expr, bounds=node.bounds)

#     def visit_LetTuple(self, node: LetTuple) -> LetTuple:
#         y = self._find(node.y)
#         e = self.visit(node.e)
#         if y is node.y and e is node.e: return node
#         return LetTuple(node.xs, node.ts, y, e, bounds=node.bounds)

#     def visit_LetRec(self, node: LetRec) -> LetRec:
#         body = self.visit(node.f.body)
#         f = node.f.update(body=body)
#         e = self.visit(node.e)
#         return node.update(f=f, e=e)
