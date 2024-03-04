import ty
from lex import lex
from transform.syntax import Parser
from id import Id
from bounds import Bounds
from transform.syntax import Typing, Monomorphization, KNormalizer, KNormalizerTopLevel, knormalize, InferError, \
    ExternalVariableTypeError, \
    get_typing_adapter, ParseError
from transform.knormal import ClosureConverter
from metadata import DIScope
from preludes import preludes, prelude_ty0s
from transform.closure import TypeCheck, Program, LinearScan, LIRPrinter, inline, GraphBuilder, GraphPrinter, GraphVerifier, GraphOptimizer, Assembler
import os
import sys
import argparse


def parse(*filenames: str):
    scope = DIScope()
    p = preludes.copy()
    asts = {filename: Parser(p, scope, list(lex(filename))).parse_toplevel() for filename in filenames}
    return asts


def main(*filenames: str):
    assert len(set(filenames)) == len(filenames), "duplicate filenames"
    try:
        asts = parse(*filenames)
    except RuntimeError as e:
        exit(1)
    except ParseError as e:
        print(e.dump(), file=sys.stderr)
        exit(1)

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
    if argv.print_type:
        print('number of user defined functions:', len(funcs))
        for f in typing_visitor.funcs:
            print(f"{repr(f)}({str(f)}): {funcs[f]}")

    k_normalizer = KNormalizerTopLevel(KNormalizer(mono, funcs))
    try:
        kns = knormalize(k_normalizer, **asts)
    except ExternalVariableTypeError:
        return
    if argv.print_knormal:
        for filename in filenames:
            with open(f"{filename.removesuffix('.ml')}.knormal.ml", 'w') as f:
                for x in k_normalizer.seq[filename]:
                    print(x, file=f)

    array_makes = {k: mono.visit(v)[0] for k, v in typing_visitor.expr_visitor.array_makes.items()}
    prelude_tys = {k: mono.visit(v)[0] for k, v in prelude_ty0s.items()}
    cc = ClosureConverter(prelude_tys | array_makes)
    toplevel, es = cc.convert(*sum(kns.values(), []))
    prog = Program(tuple(toplevel), *es)
    prog = inline(prog, argv.inline)
    if argv.print_closure:
        closure_ml = f"{argv.o.removesuffix('.s')}.closure.ml"
        with open(closure_ml, 'w') as f:
            print(prog, file=f)
    builtins = prelude_tys | array_makes
    TypeCheck(builtins, cc.global_vars).test_program(prog)
    # Count(builtins).set_globals(cc.global_vars).count_program(prog)
    gm = GraphBuilder(prelude_tys, array_makes, cc.global_vars, prog)
    gp = GraphPrinter()
    gv = GraphVerifier()
    go = GraphOptimizer()
    out = open(argv.o, 'w')
    out_buf: dict[str, str] = {}
    for f in {gm.main.name: gm.main, **gm.functions}.values():
        gv.verify(f)
        go.remove_indirect_jumps(f.entry, set())
        gv.verify(f)
        go.remove_unused_values(f)
        gv.verify(f)
        go.loop_transformation(f)
        gv.verify(f)
        if gv.has_critical_edge(f):
            go.split_critical_edges(f)
            gv.verify(f)
            assert not gv.has_critical_edge(f)
        f.gen_lir()
        ls = LinearScan(f)
        ls.do_linear_scan()
        filename = 'main' if f.name.is_main() else f.name
        if argv.print_ir:
            with open(f"{filename}.ir", 'w') as file:
                gp.print_function(f, {b.block_id: b for b in ls.blocks}, file)
                lp = LIRPrinter(file)
                lp.print_function(ls)

        asm = Assembler(ls)
        if not f.name.is_main():
            assert str(f.name) not in out_buf
            out_buf[str(f.name)] = '\n'.join(asm.emit_function())
        else:
            assert 'main' not in out_buf
            out_buf['main'] = '\n'.join(asm.emit_function())
            
    out.write(out_buf['main'])
    out.write('\n')
    del out_buf['main']
    for k, v in sorted(out_buf.items(), key=lambda x: x[0]):
        out.write(v)
        out.write('\n')

    from struct import pack, unpack
    for k, v in Assembler.float_table.items():
        k = unpack('f', pack('f', k))[0]
        out.write(f".globl {v}\n{v}: \n    .float {repr(k)}\n\n")
        
    for k, v in gm.globals.items():
        out.write(f".globl {k}\n{k}: \n    .zero {v.abi_size * 4}\n\n")

    out.close()
    return


def inline_size(x: str):
    x_ = int(x)
    if x_ < 0 or 20 < x_:
        raise argparse.ArgumentTypeError("inline size must be in the range [0, 20]")
    return x_


def output_file(x: str):
    if not x.endswith('.s'):
        raise argparse.ArgumentTypeError("output file must end with '.s'")
    return x


argparser = argparse.ArgumentParser(description="MinCaml compiler, version 1.0.0")
argparser.add_argument('files', nargs='+', help='input files')
argparser.add_argument('--version', action='version', version='%(prog)s 1.0.0')
argparser.add_argument('-o', metavar='FILE', type=output_file, help='output file. If not specified, the last file is used with the .s extension')
argparser.add_argument('--inline',
                       metavar='SIZE', type=inline_size,
                       help='max size of function to inline, must be in the range [0, 20]. default 20.', default=20)
argparser.add_argument('--print-ir', action='store_true', help="""
generate a .ir file for each function, containing the HIR, LIR, and the register allocation result.
""")
argparser.add_argument('--print-knormal', action='store_true', help='print the k-normalized program separately for each file')
argparser.add_argument('--print-closure', action='store_true',
                       help='print the closure-converted program to <last file or \'-o\'-specified file>.closure.ml')
argparser.add_argument('--print-type', action='store_true', help='print the type of each function')

if __name__ == '__main__':
    argv = argparser.parse_args(sys.argv[1:])

    if (arg := next((arg for arg in argv.files if not arg.endswith('.ml')), None)) is not None:
        print(f"error: {arg}: must end with '.ml'", file=sys.stderr)
        sys.exit(1)
    if argv.o is None:
        argv.o = f"{argv.files[-1].removesuffix('.ml')}.s"
    path = argv.files
    Bounds.srcs = list(path)
    main(*path)
