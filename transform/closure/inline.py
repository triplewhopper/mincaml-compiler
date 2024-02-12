from .language import Exp, Lit, LitF, Var, Get, Unary, AppCls, AppDir, Binary, Seq, Tuple, Put, If, Let, LetTuple, \
    MakeCls, Function, Cls, LetBinding, Program
from ty import Ty, TyUnit, TyInt, TyBool, TyFloat
from id import Id
from opkinds import UnaryOpKind, BinaryOpKind
from collections.abc import MutableMapping, Mapping

def collect_callsites(e: Exp[Ty], acc: set[Id]):
    match e:
        case AppDir(callee, _args):
            acc.add(callee)
        case Seq(es):
            for e in es:
                collect_callsites(e, acc)
        case If(_cond, br_true, br_false):
            collect_callsites(br_true, acc)
            collect_callsites(br_false, acc)
        case Let(b, expr):
            collect_callsites(b.rhs, acc)
            collect_callsites(expr, acc)
        case LetTuple(_xs, _ts, _y, e):
            collect_callsites(e, acc)
        case MakeCls(_, body):
            collect_callsites(body, acc)
        case _:
            ...

def size(e: Exp[Ty], /) -> int:
    match e:
        case Seq(es):
            return sum(size(e) for e in es)
        case If(_cond, br_true, br_false):
            return 1 + size(br_true) + size(br_false)
        case Let(_, expr):
            return 1 + size(expr)
        case LetTuple(_xs, _ts, _y, expr):
            return 1 + size(expr)
        case MakeCls(_, body):
            return 1 + size(body)
        case _:
            return 1
        
def alpha(e: Exp[Ty], s: MutableMapping[Id, Id]) -> Exp[Ty]:
    """alpha-renaming of variables in the expression `e` using the substitution `s`"""
    match e:
        case Lit():
            return e
        case Var(name):
            name_ = s.get(name, name)
            return e if name_ is name else Var(name_, e.typ)
        case Get(array, index):
            array_=s.get(array, array)
            index_=s.get(index, index)
            return e if array_ is array and index_ is index else Get(array_, index_, typ=e.typ)
        case Unary(op, e1):
            e1_ = s.get(e1, e1)
            return e if e1_ is e1 else Unary(op, e1_)
        case AppCls(callee, args):
            if callee not in s and s.keys().isdisjoint(args):
                return e
            callee_ = s.get(callee, callee)
            args_ = tuple(s.get(arg, arg) for arg in args)
            return AppCls(callee_, args_, typ=e.typ)
        case AppDir(callee, args):
            if callee not in s and s.keys().isdisjoint(args):
                return e
            callee_ = s.get(callee, callee)
            args_ = tuple(s.get(arg, arg) for arg in args)
            return AppDir(callee_, args_, typ=e.typ)
        case Binary(op, y1, y2):
            y1_ = s.get(y1, y1)
            y2_ = s.get(y2, y2)
            return e if y1_ is y1 and y2_ is y2 else Binary(op, y1_, y2_)
        case Seq(es):
            es_ = [alpha(e, s) for e in es]
            return e if all(e_ is e for e_, e in zip(es_, es)) else Seq(*es_)
        case Tuple(ys):
            if s.keys().isdisjoint(ys):
                return e
            ys_ = tuple(s.get(y, y) for y in ys)
            return Tuple(ys_, e.typ)
        case Put(array, index, value):
            array_ = s.get(array, array)
            index_ = s.get(index, index)
            value_ = s.get(value, value)
            return e if array_ == array and index_ == index and value_ == value else Put(array_, index_, value_)
        case If(cond, br_true, br_false):
            cond_ = s.get(cond, cond)
            br_true_ = alpha(br_true, s)
            br_false_ = alpha(br_false, s)
            return e if cond_ == cond and br_true_ is br_true and br_false_ is br_false else If(cond_, br_true_, br_false_)
        case Let(b, expr):
            rhs = alpha(b.rhs, s)
            lhs = Id(f'{b.lhs}.inline')
            assert b.lhs not in s
            s[b.lhs] = lhs
            expr_ = alpha(expr, s)
            del s[b.lhs]
            return e if rhs is b.rhs and expr_ is expr else Let(LetBinding(lhs, rhs, b.is_tmp), expr_)
        case LetTuple(xs, ts, y, e):
            y_ = s.get(y, y)
            xs_ = [Id(f'{x}.inline') for x in xs]
            assert s.keys().isdisjoint(xs)
            s.update(zip(xs, xs_))
            e_ = alpha(e, s)
            for x in xs:
                del s[x]
            return LetTuple(xs_, ts, y_, e_)
        case MakeCls(Cls(entry=entry, actual_fv=actual_fv), body):
            if s.keys().isdisjoint(actual_fv):
                return e
            actual_fv_ = tuple(s.get(x, x) for x in actual_fv)
            return MakeCls(Cls(entry, actual_fv_), alpha(body, s))
        case _:
            raise NotImplementedError(e)
        
def inline_impl(e: Exp[Ty], known: Mapping[Id, Function]) -> Exp[Ty]:
    match e:
        case AppDir(callee, [y1, y2]) if callee.is_intrinsic('fless'):
            return Binary(BinaryOpKind.F_LT, y1, y2)
        case AppDir(callee, [y1, y2]) if callee.is_intrinsic('fequal'):
            return Binary(BinaryOpKind.F_EQ, y1, y2)
        case AppDir(callee, args) if callee in known:
            f = known[callee]
            s = dict(zip(f.formal_args, args, strict=True))
            return alpha(f.body, s)
        case If(cond, AppDir(callee, [arg]), Var(name)) if callee.is_intrinsic('not') and arg == name:
            from preludes import preludes
            return AppDir(preludes['xor'], [cond, arg], typ=TyBool())
        case If(cond, br_true, br_false):
            br_true_ = inline_impl(br_true, known)
            br_false_ = inline_impl(br_false, known)
            return e if br_true_ is br_true and br_false_ is br_false else If(cond, br_true_, br_false_)
        case Let(binding, expr):
            rhs_ = inline_impl(binding.rhs, known)
            expr_ = inline_impl(expr, known)
            return e if rhs_ is binding.rhs and expr_ is expr else Let(LetBinding(binding.lhs, rhs_, binding.is_tmp), expr_)
        case LetTuple(xs, ts, y, e1):
            e1_ = inline_impl(e1, known)
            return e if e1_ is e1 else LetTuple(xs, ts, y, e1_)
        case Seq(es):
            es_ = [inline_impl(e, known) for e in es]
            return e if all(e_ is e for e_, e in zip(es_, es)) else Seq(*es_)
        case _:
            return e

def get_call_graph(prog: Program):
    call_graph = {f.funct: set[Id]() for f in prog.fns}
    for f in prog.fns:
        collect_callsites(f.body, call_graph[f.funct])
    return call_graph

def inline(prog: Program) -> Program:
    """inline direct calls to known functions in the program"""
    known = {f.funct: f for f in prog.fns}
    call_graph = get_call_graph(prog)
    dfn = {f: 0 for f in known}
    low = {f: 0 for f in known}
    scc = {f: 0 for f in known}
    idx, n_scc = 0, 0
    stack: list[Id] = []
    def dfs(u: Id, /):
        nonlocal idx, n_scc
        dfn[u] = low[u] = idx
        idx += 1
        stack.append(u)
        for v in call_graph[u]:
            if v in known:
                if dfn[v] == 0:
                    dfs(v)
                    low[u] = min(low[u], low[v])
                elif v in stack:
                    low[u] = min(low[u], dfn[v])
        if dfn[u] == low[u]:
            while True:
                v = stack.pop()
                scc[v] = n_scc
                if v == u:
                    break
            n_scc += 1
        return 0
    for f in known:
        # print(f"{f}: size {size(known[f].body)}, calls {', '.join(sorted(map(str, call_graph[f])))}")
        if dfn[f] == 0:
            dfs(f)
    for f in known:
        known_ = {k: v for k, v in known.items() if scc[k] != scc[f] and size(v.body) <= 3}
        known[f].body = inline_impl(known[f].body, known_)

    call_graph = get_call_graph(prog)
    for f in known:
        print(f"{f}: size {size(known[f].body)}, calls {', '.join(sorted(map(str, call_graph[f])))}")

    exp_or_cls_or_letbindings: list[Exp[Ty] | Cls | LetBinding] = []
    for x in prog.exp_or_cls_or_letbindings:
        match x:
            case LetBinding() as b:
                exp_or_cls_or_letbindings.append(LetBinding(b.lhs, inline_impl(b.rhs, known), b.is_tmp))
            case Exp() as e:
                exp_or_cls_or_letbindings.append(inline_impl(e, known))
            case Cls() as c:
                exp_or_cls_or_letbindings.append(c)
    return Program(prog.fns, *exp_or_cls_or_letbindings)