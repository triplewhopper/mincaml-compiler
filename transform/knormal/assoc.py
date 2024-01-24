# from .language import KNormal, Seq, If, Let, LetTuple, LetRec
# from .identity import Identity
# from .visitor import KNormalVisitor
# from .. import bind_logger
# import logging

# get_adapter = bind_logger(logger=logging.getLogger(__name__))


# class Assoc(Identity):

#     def visit(self, node: KNormal) -> KNormal:
#         res = super().visit(node)
#         assert res.typ == node.typ
#         return res

#     def visit_Seq(self, node: Seq):
#         es = [self.visit(e) for e in node.es]
#         if all(e is node.es[i] for i, e in enumerate(es)):
#             return node
#         return Seq(*es)

#     def visit_If(self, node: If):
#         t = self.visit(node.br_true)
#         f = self.visit(node.br_false)
#         if t is node.br_true and f is node.br_false:
#             return node
#         return If(node.cond, t, f, bounds=node.bounds)

#     def visit_Let(self, node: Let):
#         def insert(kn: KNormal):
#             if isinstance(kn, Let):
#                 expr = insert(kn.expr)
#                 if expr is kn.expr:
#                     return kn
#                 return Let(kn.lhs, kn.rhs, expr, bounds=kn.bounds)
#             elif isinstance(kn, LetRec):
#                 e = insert(kn.e)
#                 if e is kn.e:
#                     return kn
#                 return LetRec(kn.f, e, bounds=kn.bounds)
#             elif isinstance(kn, LetTuple):
#                 e = insert(kn.e)
#                 if e is kn.e:
#                     return kn
#                 return LetTuple(kn.xs, kn.ts, kn.y, e, bounds=kn.bounds)
#             else:
#                 expr = self.visit(node.expr)
#                 if kn is node.rhs and expr is node.expr:
#                     res = node
#                 else:
#                     res = Let(node.lhs, kn, expr, bounds=node.bounds)
#                 return res

#         rhs = self.visit(node.rhs)
#         return insert(rhs)

#     def visit_LetTuple(self, node: LetTuple):
#         e = self.visit(node.e)
#         return node.update(e=e)

#     def visit_LetRec(self, node: LetRec):
#         body = self.visit(node.f.body)
#         e = self.visit(node.e)
#         return node.update(f=node.f.update(body=body), e=e)


# # class AssocTopLevel(KNormalVisitor[Assoc]):
# #     def __init__(self):
# #         super().__init__(Assoc())
# #
# #     def visit_Decl(self, node: Decl):
# #         e = self.expr_visitor.visit(node.e)
# #         if e is node.e: return node
# #         return Decl(node.x, e, bounds=node.bounds)
# #
# #     def visit_DeclRec(self, node: DeclRec):
# #         f = self.expr_visitor.visit(node.f.body)
# #         f = node.f.update(body=f)
# #         if f is node.f: return node
# #         return DeclRec(f, bounds=node.bounds)
# #
# #     def visit_TopLevel(self, node: TopLevel):
# #         decls = [self.visit(decl) for decl in node.decl_or_exprs]
# #         if all(decl is node.decl_or_exprs[i] for i, decl in enumerate(decls)):
# #             return node
# #         return TopLevel(*decls, bounds=node.bounds)
