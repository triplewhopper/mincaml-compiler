import ty
from lex import lex
from transform.syntax import Parser
from id import Id
from bounds import Bounds
from transform.syntax import Typing, Monomorphization, KNormalizer, KNormalizerTopLevel, knormalize, InferError, \
    ExternalVariableTypeError, \
    get_typing_adapter, ParseError
# from transform.knormal import Beta, get_beta_adapter
from transform.knormal import ClosureConverter #¯, get_closure_converter_adapter
# from transform.knormal import Assoc, get_assoc_adapter
# from transform.knormal import Disambiguate #, get_disambiguate_adapter
# from transform.closure import IREmitter
from transform.closure import Flatten
from metadata import DIScope
from preludes import preludes, prelude_ty0s
from transform.closure import TypeCheck, Program, Count, Select, LinearScan, AsmEmmiter, inline
import os
import sys

def parse(*filenames: str):
    scope = DIScope()
    p = preludes.copy()
    asts = {filename: Parser(p, scope, list(lex(filename))).parse_toplevel() for filename in filenames}
    return asts


def main(*filenames: str):

    assert len(set(filenames)) == len(filenames), "duplicate filenames"
    try:
        asts = parse(*filenames)
    except ParseError as e:
        print(e.dump(), file=sys.stderr)
        return

    typing_visitor = Typing(prelude_ty0s.copy())

    
    try:
        ast_tys = {k: typing_visitor.infer(v) for k, v in asts.items()}
        Id.di_vars.clear()
        for k, v in preludes.items():
            v.add_to_intrinsics(k)
        Id.di_vars.update(typing_visitor.expr_visitor.di_vars)
    except InferError:
        return

    with open(os.path.dirname(os.path.abspath(filenames[0])) + '/debuginfo.txt', 'w') as f:
        for k, v in Id.di_vars.items():
            print(f'{repr(k)}: {v}', file=f)

    mono = Monomorphization(typing_visitor.uf)
    # for v in ast_tys.values():
    #     for t in v:
    #         with get_typing_adapter(t.bounds) as adapter:
    #             t = mono.visit(t.val)[0]
    #             if not isinstance(t, ty.TyUnit):
    #                 adapter.error(f"toplevel expression does not have type unit: {t}")
    #                 return
    funcs: dict[Id, ty.TyFun] = {}
    for f in typing_visitor.funcs:
        t0 = typing_visitor.funcs[f]
        t, us = mono.visit(t0)
        assert isinstance(t, ty.TyFun)
        funcs[f] = t
        if len(us) > 0:
            with get_typing_adapter(typing_visitor.expr_visitor.di_vars[f].loc.get_bounds()) as adapter:
                adapter.warning(
                    f"this function has type {t0}: uninstantiated type variables {' '.join(map(str, us))} detected")
    print('number of user defined functions:', len(funcs))
    for f in typing_visitor.funcs:
        print(f"{repr(f)}({str(f)}): {funcs[f]}")

    k_normalizer = KNormalizerTopLevel(KNormalizer(mono, funcs))
    try:
        kns = knormalize(k_normalizer, **asts)
    except ExternalVariableTypeError:
        return
    for filename in filenames:
        with open(f"{filename.replace('.ml', '.knormal.ml')}", 'w') as f:
            for x in k_normalizer.seq[filename]:
                print(x, file=f)
    # beta = BetaTopLevel()
    # assoc = AssocTopLevel()
    # for filename, kn in kns.items():
    #     kn = beta.visit_TopLevel(kn)
    #     kn = assoc.visit_TopLevel(kn)
    #     with open(f"{filename.replace('.ml', '.assoc.ml')}", 'w') as f:
    #         print(kn, file=f)
    # disambiguate = Disambiguate(k_normalizer.known_ext_funcs)
    # for kn in sum(kns.values(), []):
    #     disambiguate.visit(kn)
    array_makes = {k: mono.visit(v)[0] for k, v in typing_visitor.expr_visitor.array_makes.items()}
    prelude_tys = {k: mono.visit(v)[0] for k, v in prelude_ty0s.items()}
    cc = ClosureConverter(prelude_tys | array_makes)
    toplevel, es = cc.convert(*sum(kns.values(), []))
    prog = Program(tuple(toplevel), *es)
    prog = inline(prog)
    with open(f"main.closure.ml", 'w') as f:
        for fn in prog.fns:
            print(fn, file=f)
        for x in es:
            print(x, file=f)
    builtins = prelude_tys | array_makes
    TypeCheck(builtins, cc.global_vars).test_program(prog)
    Count(builtins).set_globals(cc.global_vars).count_program(prog)
    select = Select(prelude_tys, array_makes, cc.global_vars)
    code, main = select.select_program(prog)
    code = {main.funct: main, **code}
    with open(os.path.dirname(filenames[0]) + '/main.s', 'w') as f:
        for mf in code:
            ls = LinearScan(set(prelude_tys) | set(am.funct for am in select.array_make_cache.values()), main.global_var_addr)
            live_intervals, favor, live_across_call = ls.analyze_liveness(code[mf])
            register, location = ls.linear_scan(code[mf])
            print(f'function {mf}: {code[mf].typ}')
            for i in live_intervals:
                if i in register:
                    print(f'  {i}: {live_intervals[i]}, live_across_call?: {live_across_call[i]}, {register[i]} {favor.get(i, "")}')
                else:
                    print(f'  {i}: {live_intervals[i]}, live_across_call?: {live_across_call[i]}, fp[{location[i]}] {favor.get(i, "")}')
            asmemmiter = AsmEmmiter(builtins, cc.global_vars, main.global_var_addr)
            asm = asmemmiter.emit_asm(register, location, code[mf])
            print('\n'.join(asm), file=f)

        for array_make in select.array_make_cache.values():
            asmemmiter = AsmEmmiter(builtins, cc.global_vars, main.global_var_addr)
            asm = asmemmiter.emit_asm({}, {}, array_make)
            print('\n'.join(asm), file=f)
        
        asm_global_vars: dict[Id, int] = {}
        for x, i in main.global_var_addr.values():
            if x not in code:
                asm_global_vars[x] = max(asm_global_vars.get(x, 0), i)
        for x, i in asm_global_vars.items():
            print(f'{x.dump_as_label()}:', file=f)
            print(f'    .zero {(1 + i) * 4}', file=f)
        for k, v in main.float_table.items():
            print(f'{v.dump_as_label()}: .float {k}', file=f)
        

    return
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
    path = 'samples/raytracer/globals2.ml', 'samples/raytracer/minrt.ml',
    # path = 'test/toomanyargs.ml',
    # path = 'samples/highorder.ml',
    # path = 'samples/fib.ml',
    # path = 'samples/forever.ml',
    # path = 'samples/atomic.ml',
    # path = 'samples/ack.ml',
    # path = sys.argv[1:]
    Bounds.srcs = list(path)
    main(*path)
