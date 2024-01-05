import knormal as K
import ty
from typing import cast, Literal, List
from withbounds import WithBounds


class UnitElim(K.KNormalVisitor):
    def visit_Let(self, node: K.Let) -> List[K.KNormal]:
        if node.rhs.get_type() is ty.TyUnit():
            return [node.rhs, *self.visit(node.expr)]
        else:
            return [node]

    def visit_LetRec(self, node: K.LetRec) -> List[K.KNormal]:

