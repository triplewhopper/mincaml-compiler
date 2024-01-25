from transform.knormal.language import KNormal
from . import Lit
from .language import Var, Get, Unary, App, Binary, Seq, Tuple, Put, If, Let, LetTuple, LetRec, Function, \
    KNormal, LetBinding
from id import Id
from ty import Ty, TyFun
from withbounds import WithBounds
from .. import bind_logger
import logging

get_adapter = bind_logger(logger=logging.getLogger(__name__))


class Disambiguate:

    def __init__(self, known_ext_funcs: dict[TyFun, set[Id]]):
        _disambiguate_env: dict[str, set[TyFun]] = {}
        self._rename_env = dict[Id, Id]()
        for ftype, funcs in known_ext_funcs.items():
            for func in funcs:
                _disambiguate_env.setdefault(func.val.val, set()).add(ftype)
        _disambiguate_env2: dict[str, list[TyFun]] = {k: list(v) for k, v in _disambiguate_env.items()}
        for ftype, funcs in known_ext_funcs.items():
            removes: list[Id] = []
            adds: list[Id] = []
            for func in funcs:
                ftypes = _disambiguate_env2[func.val.val]
                if len(ftypes) > 1:
                    removes.append(func)
                    new_name = Id(WithBounds(func.val.val + str(ftypes.index(ftype)), func.bounds))
                    adds.append(new_name)
                    self._rename_env[func] = new_name
            for r in removes:
                funcs.remove(r)
            funcs.update(adds)

    def visit(self, node: KNormal[Ty] | Function | LetBinding, /) -> None:
        match node:
            case Lit() | Var() | Get() | Unary() | Binary():
                ...
            case Ext():
                node.name = self._rename_env.get(node.name, node.name)
            case App():
                node.callee = self._rename_env.get(node.callee, node.callee)
                node.args = tuple(self._rename_env.get(a, a) for a in node.args)
            case Seq(es=es):
                for e in es: self.visit(e)
            case Tuple():
                node.ys = tuple(self._rename_env.get(y, y) for y in node.ys)
            case Put():
                node.value = self._rename_env.get(node.value, node.value)
            case If():
                self.visit(node.br_true)
                self.visit(node.br_false)
            case LetBinding() as binding:
                self.visit(binding.rhs)
            case Let():
                self.visit(node.binding)
                self.visit(node.expr)
            case LetTuple():
                self.visit(node.e)
            case LetRec(f=f, e=e):
                self.visit(f.body)
                self.visit(e)
            case Function(body=body):
                self.visit(body)
            case _:
                raise NotImplementedError(f"visit_{type(node).__name__}")

