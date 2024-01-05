import ty
from lex import lex
from parse import Parser, ParseException
from infer import Typing, InferError, Monomorphization
from withbounds import WithBounds
from typing import Dict, List
from knormal import KNormalizer
from closure import ClosureConverter
from emit import IREmitter
import sys


def main(filename):
    try:
        with open(filename, 'r') as f:
            code = f.read()
            toks = list(lex(filename))
        ast = Parser(code, toks).parse_expr()
        # print(ast)
    except ParseException as e:
        import traceback
        print(e.explain(0), file=sys.stderr)
        print(file=sys.stderr)
        print(traceback.format_exc(), file=sys.stderr)
        return

    typing_visitor = Typing(code.encode('utf-8'))
    try:
        ast_ty = typing_visitor.infer(ast)
    except InferError as e:
        e.set_s(code.encode('utf-8'))
        print(e, file=sys.stderr)
        return

    mono = Monomorphization(typing_visitor.uf)
    print(mono.visit(ast_ty))
    funcs: Dict[WithBounds[str], ty.TyFun] = {f: mono.visit(typing_visitor.funcs[f]) for f in typing_visitor.funcs}

    for f in funcs:
        print(f.val, ':', funcs[f])
    del f

    k_normalizer = KNormalizer(mono, funcs)
    kn = k_normalizer.visit(ast)
    with open(f"{filename.replace('.ml', '.knormal.ml')}", 'w') as f:
        print(kn, file=f)
    cc = ClosureConverter(k_normalizer.known_ext_funcs)
    toplevel, e = cc.convert(kn)
    ir_emitter = IREmitter(k_normalizer.known_ext_funcs, k_normalizer.known_ext_arrays, toplevel, e)
    with open(filename.replace('.ml', '.ll'), 'w') as f:
        print(ir_emitter.module, file=f)


if __name__ == '__main__':
    main('samples/min-rt.ml')
