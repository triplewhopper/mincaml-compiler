import knormal as K
from ty import *
from typing import cast, Literal, List
from withbounds import WithBounds
from collections import ChainMap
import logging

logging.basicConfig(level=logging.INFO, format="%(asctime)s - %(name)s - %(levelname)s - %(message)s")
logger = logging.getLogger(__name__)


class UnitEliminator(K.KNormalVisitor[K.KNormal | None]):
    def __init__(self):
        self._env = ChainMap[K.Id, K.KNormal]()

    def visit(self, node: K.KNormal) -> K.KNormal | None:
        return super().visit(node)

    def visit_Lit(self, node: K.Lit) -> K.KNormal | None:
        if node.get_type() is TyUnit():
            logging.info(f"eliminating unit literal {node} at {node.bounds}")
            return None
        return node

    def visit_Var(self, node: K.Var) -> K.KNormal | None:
        if node.get_type() is TyUnit():
            return None
        return node

    def visit_Ext(self, node: K.Ext) -> K.KNormal:
        assert node.get_type() is not TyUnit(), f"external variable {node} does not have array type"
        return node

    def visit_Get(self, node: K.Get) -> K.KNormal | None:
        match self._env[node.array].get_type():
            case TyArray(TyUnit()):
                logger.warning(f"aggressively eliminating unit array read access {node}")
                return None
            case _:
                return node

    def visit_Unary(self, node: K.Unary) -> K.KNormal:
        assert node.get_type() is not TyUnit()
        return node

    def visit_App(self, node: K.App) -> K.KNormal:
        if any(self._env[x].get_type() is TyUnit() for x in node.args):
            non_unit_args = []
            eliminated_args = []
            for x in node.args:
                kn = self._env[x]
                if kn.get_type() is TyUnit():
                    eliminated_args.append(x)
                else:
                    non_unit_args.append((x, kn))
            if not non_unit_args:
                with K.App.relax_min_n_args():
                    res = K.App(node.callee, self._env[node.callee])
            else:
                res = K.App(node.callee, self._env[node.callee], *non_unit_args)
            logger.info(f"eliminating unit argument(s): {node} => {res}")
            return res
        return node

    def visit_Binary(self, node: K.Binary) -> K.KNormal:
        return node

    def visit_Tuple(self, node: K.Tuple) -> K.KNormal:
        if any(self._env[x].get_type() is TyUnit() for x in node.elems):
            non_unit_elems = []
            eliminated_elems = []
            for x in node.elems:
                kn = self._env[x]
                if kn.get_type() is TyUnit():
                    eliminated_elems.append(x)
                else:
                    non_unit_elems.append((x, kn))
            match non_unit_elems:
                case []:
                    res = K.Lit.unit_with_bounds(node.bounds)
                case [(_, kn)]:
                    res = kn
                case _:
                    res = K.Tuple(*non_unit_elems)
            logger.info(f"eliminating unit element(s): {node} => {res}")
            return res
        return node

    def visit_Put(self, node: K.Put) -> K.KNormal | None:
        match self._env[node.array].get_type():
            case TyArray(TyUnit()):
                # res = K.Lit(WithBounds(cast(Literal['()'], '()'), node.bounds))
                logger.warning(f"aggressively eliminating unit array write access: {node}")
                return None
            case _:
                return node

    def visit_If(self, node: K.If) -> K.KNormal | None:
        br_true = self.visit(node.br_true)
        br_false = self.visit(node.br_false)
        if br_true is node.br_true and br_false is node.br_false:
            return node
        if br_true is None and br_false is None:
            return None
        if br_true is None:
            br_true = K.Lit.unit_with_bounds(node.br_true.bounds)
        if br_false is None:
            br_false = K.Lit.unit_with_bounds(node.br_false.bounds)
        return K.If((node.cond, self._env[node.cond]), br_true, br_false, node.bounds)

    def visit_Let(self, node: K.Let) -> K.KNormal:
        rhs = self.visit(node.rhs)
        expr = self.visit(node.expr)
        if rhs is node.rhs and expr is node.expr:
            return node
        if rhs.get_type() is TyUnit():
            match rhs, expr:
                case K.Seq(), K.Seq():
                    return K.Seq(*rhs.es, *expr.es)
                case K.Seq(), _:
                    return K.Seq(*rhs.es, expr)
                case _, K.Seq():
                    return K.Seq(rhs, *expr.es)
                case _, _:
                    return K.Seq(rhs, expr)
        else:
            expr = self.visit(node.expr)
            if expr is node.expr:
                return node
            else:
                return K.Let(node.lhs, rhs, expr, node.bounds)

    def visit_LetRec(self, node: K.LetRec) -> List[K.KNormal]:
