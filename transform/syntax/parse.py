from collections.abc import Callable
from typing import Type, TypeVar, overload, Literal, LiteralString

from . import language
from .errors import UnexpectedTokenError, DuplicateVariableError, WildcardNotAllowedError, \
    ExpectLowercaseIdentifierError, ExpectUppercaseIdentifierError, WildcardCannotBeFunctionNameError, \
    FunctionDefinedWithNoParametersError, UnmatchedParenthesesError, TrailingLambdaNotParenthesizedError, \
    UnBoundVariableError
from lex import Val, Word, EOF
from withbounds import WithBounds
from id import Id
from metadata import DIScope, DILocation, DIVariable
from collections import ChainMap
import contextlib

T = TypeVar("T", bound=language.Expr)
U = TypeVar("U", int, float, bool)
S = TypeVar("S", bound=LiteralString)


def check_linearity(*names: WithBounds[str]) -> None:
    table: set[str] = set()
    for w in names:
        if w.val != '_':
            if w.val not in table:
                table.add(w.val)
            else:
                raise DuplicateVariableError(word=w)


class Parser:
    def __init__(self, env: dict[str, Id], scope: DIScope, tokens: list[Val | Word | EOF]):
        assert len(tokens) > 0 and isinstance(tokens[-1], EOF)
        self.tokens = tokens
        self.i = 0
        self.eof = tokens[-1]
        self.env = ChainMap(env)
        self.scope = scope

    @contextlib.contextmanager
    def new_child_env(self, env: dict[str, Id] | None = None):
        self.env = self.env.new_child(env)
        scope, self.scope = self.scope, DIScope(self.scope)
        try:
            yield self.scope
        finally:
            self.env = self.env.parents
            self.scope = scope

    def peek(self, offset: int = 0):
        assert offset >= 0
        try:
            return self.tokens[self.i + offset]
        except IndexError:
            return self.eof

    def di_var(self, tok: WithBounds[str]):
        return DIVariable.from_wbs(self.scope, tok)

    def var_of_new_id(self, tok: WithBounds[str]):
        return language.Var(Id(), self.di_var(tok))

    def consume(self, n: int = 1):
        assert n >= 1
        if self.i + n < len(self.tokens):
            self.i += n
        else:
            self.i = len(self.tokens)

    def match(self, what: str) -> None:
        """:raises UnexpectedTokenError: if the current token does not match `what`"""
        if not self.peek().match(what):
            raise UnexpectedTokenError(expected=what, bounds=self.peek().bounds)
        self.consume()

    def match_with_bounds(self, what: S) -> WithBounds[S]:
        """:raises ParseException: if the current token does not match `what`"""
        if not self.peek().match(what):
            raise UnexpectedTokenError(expected=what, bounds=self.peek().bounds)
        bounds = self.peek().bounds
        self.consume()
        return WithBounds[S](what, bounds)

    def parse_ident(self, capitalized: bool = False, allow_underscore: bool = False) -> WithBounds[str]:
        """
        :raises ExpectLowercaseIdentifierError
        :raises ExpectUppercaseIdentifierError
        :raises WildcardNotAllowedError
        """
        b = self.peek().bounds
        try:
            ident = self.peek().get_ident(capitalized)
            if ident == '_' and not allow_underscore:
                raise WildcardNotAllowedError(bounds=b)
            self.consume()
            return WithBounds(ident, b)
        except ValueError:
            if capitalized:
                raise ExpectUppercaseIdentifierError(bounds=b)
            raise ExpectLowercaseIdentifierError(bounds=b)

    def match_val(self, ty: Type[U]) -> WithBounds[U]:
        b = self.peek().bounds
        try:
            res = WithBounds(self.peek().get_val(ty), b)
            self.consume()
            return res
        except ValueError:
            raise UnexpectedTokenError(expected=ty.__name__, bounds=b)

    def parse_toplevel(self):
        decl_or_exprs: list[language.Decl | language.DeclRec | language.Expr] = []
        while not isinstance(self.peek(), EOF):
            decl_or_exprs.append(d := self.parse_expr(on_toplevel=True))
            if self.peek().match(';;'):
                self.consume()
            if isinstance(d, language.Decl):
                self.env[d.binding.var.metadata.name] = d.binding.var.name

            elif isinstance(d, language.DeclRec):
                self.env[d.f.funct.metadata.name] = d.f.funct.name

        return language.TopLevel(tuple(decl_or_exprs))

    def parse_parens(self, allow_unit: bool = False) -> language.Expr:
        b = self.match_with_bounds('(').bounds
        match self.peek():
            case Word(')') as r if allow_unit:
                self.consume()
                b |= r.bounds
                return language.LitU(DILocation(self.scope, b))
            case _:
                e = self.parse_expr()
                self.match(')')
                return e

    @overload
    def parse_let(self, on_toplevel: Literal[False] = False) -> language.Let | language.LetRec | language.LetTuple:
        ...

    @overload
    def parse_let(self, on_toplevel: Literal[True]) -> (
            language.Decl | language.DeclRec | language.Let | language.LetRec | language.LetTuple):
        ...

    def parse_let(self, on_toplevel: Literal[True, False] = False):
        _let = self.match_with_bounds('let')
        match self.peek():
            case Word('rec'):
                _rec = self.match_with_bounds('rec')
                tok_func = self.parse_ident()
                if tok_func.val == '_':
                    raise WildcardCannotBeFunctionNameError(bounds=tok_func.bounds)
                tok_args: list[WithBounds[str]] = []
                while True:
                    try:
                        tok_args.append(self.parse_ident(allow_underscore=True))
                    except ExpectLowercaseIdentifierError:
                        break
                if len(tok_args) == 0:
                    raise FunctionDefinedWithNoParametersError(bounds=tok_func.bounds)
                check_linearity(*tok_args)
                self.match('=')

                with self.new_child_env():
                    func = self.var_of_new_id(tok_func)
                    self.env[tok_func.val] = func.name

                    with self.new_child_env():
                        args = tuple([self.var_of_new_id(arg) for arg in tok_args])
                        self.env.update({tok.val: arg.name for tok, arg in zip(tok_args, args)})
                        e1 = self.parse_expr()

                    if on_toplevel:
                        match self.peek():
                            case Word(';;' | 'let') | EOF():
                                function = language.Function(func, args, e1)
                                return language.DeclRec(function)
                            case _:
                                ...

                    function = language.Function(func, args, e1)
                    self.match('in')
                    e2 = self.parse_expr()

                return language.LetRec(function, e2)
            case Word('('):
                self.consume()
                tok_args = []
                while True:
                    try:
                        tok_args.append(self.parse_ident(allow_underscore=True))
                    except ExpectLowercaseIdentifierError:
                        raise UnexpectedTokenError(expected=['lowercase identifier', '_'], bounds=self.peek().bounds)
                    match self.peek():
                        case Word(','):
                            self.consume()
                        case Word(')'):
                            break
                        case _:
                            raise UnexpectedTokenError(expected=[',', ')'], bounds=self.peek().bounds)

                assert len(tok_args) >= 2
                check_linearity(*tok_args)
                self.match(')')
                self.match('=')
                e1 = self.parse_expr()
                self.match('in')
                with self.new_child_env():
                    args = tuple(self.var_of_new_id(arg) for arg in tok_args)
                    self.env.update({tok.val: arg.name for tok, arg in zip(tok_args, args)})
                    e2 = self.parse_expr()
                    return language.LetTuple(args, e1, e2)
            case Word(_):
                tok_var = self.parse_ident(allow_underscore=True)
                self.match('=')
                e1 = self.parse_expr()
                with self.new_child_env():
                    var = self.var_of_new_id(tok_var)
                    if tok_var.val != '_':
                        self.env[tok_var.val] = var.name

                    if on_toplevel:
                        match self.peek():
                            case Word(';;' | 'let') | EOF():
                                let_binding = language.LetBinding(var, e1)
                                return language.Decl(let_binding)
                            case _:
                                ...
                    let_binding = language.LetBinding(var, e1)
                    self.match('in')
                    e2 = self.parse_expr()
                return language.Let(let_binding, e2)
            case _:
                raise UnexpectedTokenError(expected=['rec', '(', 'identifier'], bounds=self.peek().bounds)

    @overload
    def parse_expr(self, on_toplevel: Literal[False] = False) -> language.Expr:
        ...

    @overload
    def parse_expr(self, on_toplevel: Literal[True]) -> language.Decl | language.DeclRec | language.Expr:
        ...

    def parse_expr(self, on_toplevel: Literal[True, False] = False):
        match self.peek():
            case Word('let'):
                if on_toplevel:
                    return self.parse_let(on_toplevel)
                return self.parse_let(on_toplevel)
            case Word('fun'):
                raise NotImplementedError()
            case _:
                return self.parse_semi()

    def parse_semi(self) -> language.Expr:
        es: list[language.Expr] = []
        if self.peek().match('if'):
            es.append(self.parse_if())
        else:
            es.append(self.parse_put())
        while self.peek().match(';'):
            _semi = self.match_with_bounds(';')
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
            assert isinstance(es[0], language.Expr)
            return es[0]
        else:
            return language.Semi(tuple(es))

    def parse_if(self) -> language.If:
        _if_tok = self.match_with_bounds('if')
        e1 = self.parse_expr()
        self.match('then')
        e2 = self.parse_expr()
        self.match('else')
        e3 = self.parse_let_fun_if_or(lambda: self.parse_put())
        return language.If(e1, e2, e3)

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
                    raise UnmatchedParenthesesError(bounds=self.peek(n0).bounds)
                case _:
                    ...
            n += 1
        return n

    def try_parse_fun(self):
        if self.peek().match('fun'):
            raise NotImplementedError()
        return None

    def parse_put(self, guaranteed: int | None = None) -> language.Expr:
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

        if (tot := guaranteed or is_put_lhs()) is not None:
            lhs = self.parse_parens() if self.peek().match('(') else self.parse_var()
            for _ in range(tot - 1):
                self.match('.')
                _lparen = self.match_with_bounds('(')
                e = self.parse_expr()
                _rparen = self.match_with_bounds(')')
                lhs = language.Get(lhs, e)
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
            return language.Put(lhs, idx, rhs)
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
                    raise UnexpectedTokenError(expected="expression", bounds=self.peek().bounds)

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
                        raise UnexpectedTokenError(expected=[',', ')'], bounds=self.peek().bounds)
            except UnexpectedTokenError:
                break
        assert len(es) >= 2
        return language.Tuple(tuple(es))

    def parse_cmp(self) -> language.Expr:
        e1 = self.parse_addsub()
        while True:
            match self.peek():
                case Word('<' | '<=' | '>' | '>=' | '=' | '<>' as op):
                    op = self.match_with_bounds(op)
                    e2 = self.parse_let_fun_if_or(self.parse_addsub)
                    loc = DILocation(self.scope, op.bounds)
                    e1 = language.Binary(loc, op.val, e1, e2)
                case _:
                    return e1

    def parse_let_fun_if_or(self, f: Callable[[], T]) -> language.Expr:
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
                    loc = DILocation(self.scope, op.bounds)
                    e1 = language.Binary(loc, op.val, e1, e2)
                case _:
                    return e1

    def parse_muldiv(self):
        e1 = self.parse_unary()
        while True:
            match self.peek():
                case Word('*' | '/' | '*.' | '/.' as op):
                    op = self.match_with_bounds(op)
                    e2 = self.parse_let_fun_if_or(self.parse_unary)
                    loc = DILocation(self.scope, op.bounds)
                    e1 = language.Binary(loc, op.val, e1, e2)
                case _:
                    return e1

    def parse_unary(self):
        match self.peek():
            case Word('-' | '-.' as op):
                assert op in ('-', '-.')
                op = self.match_with_bounds(op)
                e = self.parse_let_fun_if_or(self.parse_unary)
                loc = DILocation(self.scope, op.bounds)
                return language.Unary(loc, op.val, e)
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
                    case Word('if' | '_' | '<-' | 'rec' | '.'):
                        raise UnexpectedTokenError(expected=[], bounds=self.peek().bounds)
                    case Word('fun'):
                        raise TrailingLambdaNotParenthesizedError(bounds=self.peek().bounds)
                    case _:
                        ...
                e = language.App(e, tuple(args))
            else:
                return e

    def parse_get(self) -> language.Get | language.Expr:
        """parse a get expression, e.g. `a.(b)` or `a.(b).(c)`"""
        e = self.parse_atomic()
        while True:
            match self.peek():
                case Word('.'):
                    self.consume()
                    _lparen = self.match_with_bounds('(')
                    idx = self.parse_expr()
                    _rparen = self.match_with_bounds(')')
                    e = language.Get(e, idx)
                case _:
                    return e

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
                return self.parse_var()
            case Word(_) as w if w.is_ident(capitalized=True):
                path = [self.parse_ident(capitalized=True)]
                self.match('.')
                while self.peek().is_ident(capitalized=True):
                    self.parse_ident(capitalized=True)
                    if self.peek().match('.'):
                        self.consume()
                    else:
                        break
                path.append(self.parse_ident())
                b = path[0].bounds
                for i in range(1, len(path)):
                    b |= path[i].bounds
                tok_var = WithBounds('.'.join(w.val for w in path), b)
                try:
                    if tok_var.val == 'Array.make':
                        return language.Var(Id(), self.di_var(tok_var))
                    return language.Var(self.env[tok_var.val], self.di_var(tok_var))
                except KeyError:
                    raise UnboundLocalError(tok_var.val)
            case Val(bool()):
                v = self.match_val(bool)
                return language.LitB(DILocation(self.scope, v.bounds), v.val)
            case Val(int()):
                v = self.match_val(int)
                return language.LitI(DILocation(self.scope, v.bounds), v.val)
            case Val(float()):
                v = self.match_val(float)
                return language.LitF(DILocation(self.scope, v.bounds), v.val)
            case Val(_):
                raise NotImplementedError()
            case _:
                raise UnexpectedTokenError(expected="atomic expression", bounds=self.peek().bounds)

    def parse_var(self):
        ident = self.parse_ident()
        try:
            return language.Var(self.env[ident.val], self.di_var(ident))
        except KeyError:
            raise UnBoundVariableError(word=ident)
