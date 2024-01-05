import logging
from typing import List, Literal, Type, TypeVar, Callable, overload, cast

from pyparsing import *

import syntax
from lex import lex, Val, Word, EOF
from withbounds import WithBounds

logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(name)s - %(levelname)s - %(message)s')
logger = logging.getLogger(__name__)

T = TypeVar("T", bound=syntax.Node)
U = TypeVar("U", int, float, bool)
S = TypeVar("S", bound=str)


def info(f):
    def wrapper(*args, **kwargs):
        res = f(*args, **kwargs)
        logger.info(f"{f.__name__}: {res}")
        return res

    return wrapper


def check_linearity(source: str, *names: WithBounds[str]) -> None:
    table = set()
    for w in names:
        if w.val != '_':
            if w.val in table:
                raise ParseException(source, msg=f"duplicate variable {w.val}", loc=w.bounds[0])
            table.add(w.val)


class Parser:
    # TODO: s should be bytes, because tokens loc is counted in bytes (ocamllex does not support unicode)
    def __init__(self, s: str, tokens: List[Val | Word]):
        assert len(tokens) > 0
        self.tokens = tokens
        self.s = s
        self.i = 0

    def peek(self, offset: int = 0) -> Val | Word | EOF:
        assert offset >= 0
        try:
            return self.tokens[self.i + offset]
        except IndexError:
            last = self.tokens[-1]
            return EOF(last.loc + len(last.text))

    def consume(self, n: int = 1):
        assert n >= 1
        if self.i + n < len(self.tokens):
            self.i += n
        else:
            self.i = len(self.tokens)

    def match(self, what: str) -> None:
        """:raises ParseException: if the next token does not match `what`"""
        if not self.peek().match(what):
            raise ParseException(self.s, self.peek().loc, f"expected '{what}'")
        self.consume()

    def match_with_bounds(self, what: S) -> WithBounds[S]:
        """:raises ParseException: if the current token does not match `what`"""
        if not self.peek().match(what):
            raise ParseException(self.s, self.peek().loc, f"expected '{what}'")
        bounds = self.peek().bounds
        self.consume()
        return WithBounds(what, bounds)

    def parse_ident(self, capitalized: bool = False, allow_underscore=False) -> WithBounds[str]:
        """:raises ParseException: if the current token is not an identifier"""
        try:
            loc, ident = self.peek().loc, self.peek().get_ident(capitalized)
            if ident == '_' and not allow_underscore:
                raise ParseException(self.s, loc, "wildcard '_' is not allowed here")
            self.consume()
            return WithBounds(ident, (loc, loc + len(ident)))
        except ValueError:
            raise ParseException(self.s, self.peek().loc, "expected identifier")

    @overload
    def match_val(self, ty: Type[int]) -> WithBounds[int]:
        ...

    @overload
    def match_val(self, ty: Type[float]) -> WithBounds[float]:
        ...

    @overload
    def match_val(self, ty: Type[bool]) -> WithBounds[bool]:
        ...

    def match_val(self, ty):
        try:
            res = WithBounds(self.peek().get_val(ty), self.peek().bounds)
            self.consume()
            return res
        except ValueError:
            raise ParseException(self.s, self.peek().loc, f"expected '{ty.__name__}'")

    def parse_parens(self, allow_unit: bool = False):
        lparen = self.match_with_bounds('(').bounds[0]
        match self.peek():
            case Word(')') as r if allow_unit:
                self.consume()
                return syntax.Lit(WithBounds(cast("Literal['()']", '()'), (lparen, r.bounds[1])))
            case _:
                e = self.parse_expr()
                self.match(')')
                return e

    def parse_let(self):
        let = self.match_with_bounds(cast("Literal['let']", 'let'))
        match self.peek():
            case Word('rec'):
                rec = self.match_with_bounds(cast("Literal['rec']", 'rec'))
                func = self.parse_ident()
                if func.val == '_':
                    raise ParseException(self.s, func.bounds[0], "function name cannot be '_'")
                args = []
                while True:
                    try:
                        arg = self.parse_ident(allow_underscore=True)
                        args.append(arg)
                    except ParseException:
                        break
                if len(args) < 1:
                    raise ParseException(self.s, self.peek().loc, "function must have at least 1 argument")
                assert len(args) > 0
                check_linearity(self.s, *args)
                self.match('=')
                e1 = self.parse_expr()
                self.match('in')
                e2 = self.parse_expr()
                function = syntax.Function(let, rec, func, args, e1)
                return syntax.LetRec(function, e2)
            case Word('('):
                self.consume()
                args = []
                while True:
                    try:
                        args.append(self.parse_ident(allow_underscore=True))
                    except ParseException:
                        raise ParseException(self.s, self.peek().loc, "expected identifier or '_'")
                    match self.peek():
                        case Word(','):
                            self.consume()
                        case Word(')'):
                            break
                        case _:
                            raise ParseException(self.s, self.peek().loc, "expected ',' or ')'")

                assert len(args) >= 2
                check_linearity(self.s, *args)
                self.match(')')
                self.match('=')
                e1 = self.parse_expr()
                self.match('in')
                e2 = self.parse_expr()
                return syntax.LetTuple(let, args, e1, e2)
            case Word(_):
                var = self.parse_ident(allow_underscore=True)
                self.match('=')
                e1 = self.parse_expr()
                self.match('in')
                e2 = self.parse_expr()
                return syntax.Let(let, var, e1, e2)
            case _:
                raise ParseException(self.s, self.peek().loc, "expected 'rec', '(' or identifier")

    def parse_expr(self):
        match self.peek():
            case Word('let'):
                return self.parse_let()
            case Word('fun'):
                raise NotImplementedError()
            case _:
                return self.parse_semi()

    def parse_semi(self) -> syntax.If | syntax.Put | syntax.Semi:
        es = []
        if self.peek().match('if'):
            es.append(self.parse_if())
        else:
            es.append(self.parse_put())
        while self.peek().match(';'):
            semi = self.match_with_bounds(cast("Literal[';']", ';'))
            # es.append(semi)
            match self.peek():
                case Word('let'):
                    es.append(self.parse_let())
                case Word('fun'):
                    raise NotImplementedError()
                case Word('if'):
                    es.append(self.parse_if())
                case _:
                    es.append(self.parse_put())
        if len(es) == 1:
            assert isinstance(es[0], syntax.Node)
            return es[0]
        else:
            return syntax.Semi(tuple(es))

    def parse_if(self):
        if_tok = self.match_with_bounds(cast("Literal['if']", 'if'))
        e1 = self.parse_expr()
        self.match('then')
        e2 = self.parse_expr()
        self.match('else')
        e3 = self.parse_let_fun_if_or(lambda: self.parse_put())
        return syntax.If(if_tok, e1, e2, e3)

    def skip_parens(self, n0: int = 0) -> int:
        """
        skip the parens from `peek(n0)` to the matching ')', return the position right after the ')'.

        for example, if the token list is

        ['c', '(', 'a', '(', 'b', ')', 'c', ')', ...]

        , then `skip_parens(1)` returns 8.

        :raises ParseException: if the parens are not matched
        """
        assert self.peek(n0).match('(')
        i, n = 1, 1 + n0
        while i > 0:
            match self.peek(n):
                case Word('('):
                    i += 1
                case Word(')'):
                    i -= 1
                case EOF():
                    raise ParseException(self.s, self.peek(n0).loc, "unmatched '('")
            n += 1
        return n

    def try_parse_fun(self):
        if self.peek().match('fun'):
            raise NotImplementedError()
        return None

    def parse_put(self, garanteed: int | None = None):
        def is_put_lhs() -> int | None:
            if self.peek().match('('):
                n = self.skip_parens()
            elif self.peek().is_ident():
                n = 1
            else:
                return None
            tot = 0
            while self.peek(n).match('.') and self.peek(n + 1).match('('):
                n = self.skip_parens(n + 1)
                tot += 1
            if tot == 0:
                return None
            return tot if self.peek(n).match('<-') else None

        if (tot := garanteed or is_put_lhs()) is not None:
            lhs = self.parse_parens() if self.peek().match('(') else syntax.Var(self.parse_ident())
            for _ in range(tot - 1):
                self.match('.')
                lhs = syntax.Get(lhs, self.parse_parens())
            self.match('.')
            idx = self.parse_parens()
            self.match('<-')
            match self.peek():
                case Word('let'):
                    rhs = self.parse_let()
                case Word('fun'):
                    raise NotImplementedError()
                case Word('if'):
                    rhs = self.parse_if()
                case _ if (tot := is_put_lhs()) is not None:
                    rhs = self.parse_put(tot)
                case _:
                    rhs = self.parse_tuple()
            return syntax.Put(lhs, idx, rhs)
        else:
            return self.parse_tuple()

    def parse_tuple(self):
        def parse_arg():
            match self.peek():
                case Word('let'):
                    return self.parse_let()
                case Word('fun'):
                    raise NotImplementedError()
                case Word('if'):
                    return self.parse_if()
                case Val(float() | bool() | int()) | Word('(' | '+' | '-' | '-.'):
                    return self.parse_cmp()
                case Word(_) as w if w.is_ident():
                    return self.parse_cmp()
                case _:
                    raise ParseException(self.s, self.peek().loc, "expected expression")

        es = [self.parse_cmp()]
        if not self.peek().match(','):
            return es[0]
        while True:
            try:
                match self.peek():
                    case Word(','):
                        self.consume()
                        es.append(parse_arg())
                    case Word(')'):
                        break
                    case _:
                        raise ParseException(self.s, self.peek().loc, "expected ',' or ')'")
            except ParseException:
                break
        assert len(es) >= 2
        return syntax.Tuple(tuple(es))

    def parse_cmp(self):
        e1 = self.parse_addsub()
        while True:
            match self.peek():
                case Word('<' | '<=' | '>' | '>=' | '=' | '<>' as op):
                    assert op in ('<', '<=', '>', '>=', '=', '<>')
                    op = self.match_with_bounds(cast("Literal['<', '<=', '>', '>=', '=', '<>']", op))
                    e2 = self.parse_let_fun_if_or(self.parse_addsub)
                    e1 = syntax.Binary(op, e1, e2)
                case _:
                    return e1

    def parse_let_fun_if_or(self, f: Callable[[], T]):
        match self.peek():
            case Word('let'):
                return self.parse_let()
            case Word('fun'):
                raise NotImplementedError()
            case Word('if'):
                return self.parse_if()
            case _:
                return f()

    def parse_addsub(self):
        e1 = self.parse_muldiv()
        while True:
            match self.peek():
                case Word('+' | '-' | '+.' | '-.' as op):
                    op = self.match_with_bounds(op)
                    e2 = self.parse_let_fun_if_or(self.parse_muldiv)
                    e1 = syntax.Binary(op, e1, e2)
                case _:
                    return e1

    def parse_muldiv(self):
        e1 = self.parse_unary()
        while True:
            match self.peek():
                case Word('*.' | '/.' as op):
                    op = self.match_with_bounds(op)
                    e2 = self.parse_let_fun_if_or(self.parse_unary)
                    e1 = syntax.Binary(op, e1, e2)
                case _:
                    return e1

    def parse_unary(self):
        match self.peek():
            case Word('-' | '-.' as op):
                assert op in ('-', '-.')
                op = self.match_with_bounds(op)
                e = self.parse_let_fun_if_or(self.parse_unary)
                return syntax.Unary(op, e)
            case Word('+'):
                self.consume()
                return self.parse_let_fun_if_or(self.parse_unary)
            case _:
                return self.parse_app()

    def parse_app(self):
        e = self.parse_get()
        while True:
            if isinstance(self.peek(), Val) or self.peek().is_ident() or self.peek().match('('):
                args = [self.parse_get()]
                while isinstance(self.peek(), Val) or self.peek().is_ident() or self.peek().match('('):
                    args.append(self.parse_get())
                match self.peek():
                    case Word('let' | 'if' | '_' | '<-' | 'rec' | '.'):
                        raise ParseException(self.s, self.peek().loc, "unexpected token")
                    case Word('fun'):
                        raise ParseException(self.s, self.peek().loc, "trailing lambda must be parenthesized")
                e = syntax.App(e, *args)
            else:
                return e

    def parse_get(self):
        """parse a get expression, e.g. `a.(b)` or `a.(b).(c)`"""
        e = self.parse_atomic()
        while True:
            match self.peek():
                case Word('.'):
                    self.consume()
                    idx = self.parse_parens()
                    e = syntax.Get(e, idx)
                case _:
                    return e

    # @info
    def parse_atomic(self):
        match self.peek():
            case Word('('):
                return self.parse_parens(allow_unit=True)
            case Word('let'):
                return self.parse_let()
            case Word('fun'):
                raise NotImplementedError()
            case Word('if'):
                return self.parse_if()
            case Word(_) as w if w.is_ident():
                return syntax.Var(self.parse_ident())
            case Word(_) as w if w.is_ident(capitalized=True):
                path = [self.parse_ident(capitalized=True)]
                self.match('.')
                while self.peek().is_ident(capitalized=True):
                    self.parse_ident(capitalized=True)
                    if self.peek().match('.'):
                        self.consume()
                    else:
                        break
                try:
                    path.append(self.parse_ident())
                    return \
                        syntax.Var(WithBounds('.'.join(w.val for w in path), (path[0].bounds[0], path[-1].bounds[1])))
                except ParseException:
                    raise ParseException(self.s, self.peek().loc, "expected a lowercase identifier")
            case Val(int() | float() | bool() as x):
                return syntax.Lit(self.match_val(x.__class__))
            case Val(_):
                raise NotImplementedError()
            case _:
                raise ParseException(self.s, self.peek().loc, "expected atomic expression")

