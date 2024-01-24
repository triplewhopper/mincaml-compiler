import ty
from lex import lex
from transform.syntax import Parser
from withbounds import WithBounds
from bounds import Bounds
from transform.syntax import Typing, Monomorphization, KNormalizer, KNormalizerTopLevel, knormalize, InferError, \
    ExternalVariableTypeError, \
    get_typing_adapter, ParseError
# from transform.knormal import Beta, get_beta_adapter
from transform.knormal import ClosureConverter #¯, get_closure_converter_adapter
# from transform.knormal import Assoc, get_assoc_adapter
from transform.knormal import Disambiguate #, get_disambiguate_adapter
# from transform.closure import IREmitter
from transform.closure import Flatten
import os
import sys


def parse(*filenames: str):
    asts = {filename: Parser(list(lex(filename))).parse_toplevel() for filename in filenames}
    return asts


def main(*filenames: str):
    assert len(set(filenames)) == len(filenames), "duplicate filenames"
    try:
        asts = parse(*filenames)
    except ParseError as e:
        print(e.dump(), file=sys.stderr)
        return

    typing_visitor = Typing()

    
    try:
        ast_tys = {k: typing_visitor.infer(v) for k, v in asts.items()}
    except InferError:
        return

    mono = Monomorphization(typing_visitor.uf)
    for v in ast_tys.values():
        for t in v:
            with get_typing_adapter(t.bounds) as adapter:
                t = mono.visit(t.val)[0]
                if not isinstance(t, ty.TyUnit):
                    adapter.error(f"toplevel expression does not have type unit: {t}")
                    return

    funcs: dict[WithBounds[str], ty.TyFun] = {}
    for f in typing_visitor.funcs:
        t0 = typing_visitor.uf.apply(typing_visitor.funcs[f])
        t, us = mono.visit(t0)
        assert isinstance(t, ty.TyFun)
        funcs[f] = t
        if len(us) > 0:
            with get_typing_adapter(f.bounds) as adapter:
                adapter.warning(
                    f"this function has type {t0}: uninstantiated type variables {' '.join(map(str, us))} detected")
    print('number of functions:', len(funcs))
    for f in typing_visitor.funcs:
        print(f"{f}: {funcs[f]}")

    k_normalizer = KNormalizerTopLevel(KNormalizer(mono, funcs))
    try:
        kns = knormalize(k_normalizer, **asts)
    except ExternalVariableTypeError:
        return
    for filename in filenames:
        with open(f"{filename.replace('.ml', '.knormal.ml')}", 'w') as f:
            for x in k_normalizer.seq[filename].val:
                print(x, file=f)
    # beta = BetaTopLevel()
    # assoc = AssocTopLevel()
    # for filename, kn in kns.items():
    #     kn = beta.visit_TopLevel(kn)
    #     kn = assoc.visit_TopLevel(kn)
    #     with open(f"{filename.replace('.ml', '.assoc.ml')}", 'w') as f:
    #         print(kn, file=f)
    disambiguate = Disambiguate(k_normalizer.known_ext_funcs)
    for kn in sum(kns.values(), []):
        disambiguate.visit(kn)
    cc = ClosureConverter(k_normalizer.known_ext_funcs)
    toplevel, es = cc.convert(*sum(kns.values(), []))

    # with open(f"{filename.replace('.ml', '.closure.ml')}", 'w') as f:
    #     for x in es:
    #         print(es, file=f)
    flatten = Flatten()
    flatten.emit(k_normalizer.known_ext_funcs, k_normalizer.known_global_vars, toplevel, es)
    # ir_emitter = IREmitter()
    # ir_emitter.emit(k_normalizer.known_ext_funcs, k_normalizer.known_global_vars, toplevel, es)

    # with open(os.path.dirname(filenames[0]) + '/main.ll', 'w') as f:
    #     print(ir_emitter.module, file=f)

    with open(os.path.dirname(filenames[0]) + '/main.my.ll', 'w') as f:
        flatten.dump(f)


if __name__ == '__main__':
    # assert len(sys.argv) >= 2
    # assert all(arg.endswith('.ml') for arg in sys.argv[1:])
    # main(sys.argv[1])
    # path = 'samples/raytracer/globals2.ml', 'samples/raytracer/minrt.ml',
    # path = 'samples/highorder.ml',
    # path = 'samples/fib.ml',
    # path = 'samples/forever.ml',
    path = 'samples/atomic.ml',
    Bounds.srcs = list(path)
    main(*path)
