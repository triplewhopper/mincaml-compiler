from bounds import Bounds
from withbounds import WithBounds


class ParseError(BaseException):
    def __init__(self, msg: str, bounds: Bounds, /):
        assert isinstance(msg, str) and isinstance(bounds, Bounds)
        self.msg = msg
        self.bounds = bounds

    def dump(self):
        return self.bounds.dump_with(self.msg)


class UnexpectedTokenError(ParseError):
    def __init__(self, /, *, expected: str | list[str], bounds: Bounds):
        match expected:
            case []:
                msg = "unexpected token"
            case [x]:
                msg = f"expected {x}"
            case [*xs, x]:
                msg = ", ".join(xs) + " or " + x
            case _:
                msg = f"expected {expected}"

        super(UnexpectedTokenError, self).__init__(msg, bounds)
        self.expected = expected


class ExpectIdentifierError(UnexpectedTokenError):
    def __init__(self, /, *, bounds: Bounds):
        super(ExpectIdentifierError, self).__init__(expected="identifier", bounds=bounds)


class ExpectLowercaseIdentifierError(UnexpectedTokenError):
    def __init__(self, /, *, bounds: Bounds):
        super(ExpectLowercaseIdentifierError, self).__init__(expected="lowercase identifier", bounds=bounds)


class ExpectUppercaseIdentifierError(UnexpectedTokenError):
    def __init__(self, /, *, bounds: Bounds):
        super(ExpectUppercaseIdentifierError, self).__init__(expected="uppercase identifier", bounds=bounds)


class WildcardNotAllowedError(ParseError):
    def __init__(self, /, *, bounds: Bounds):
        super(WildcardNotAllowedError, self).__init__(f"wildcard '_' not allowed here", bounds)


class WildcardCannotBeFunctionNameError(ParseError):
    def __init__(self, /, *, bounds: Bounds):
        super(WildcardCannotBeFunctionNameError, self).__init__(f"wildcard '_' cannot be function name", bounds)


class FunctionDefinedWithNoParametersError(ParseError):
    def __init__(self, /, *, bounds: Bounds):
        super(FunctionDefinedWithNoParametersError, self).__init__(
            f"function must be defined with at least one parameter", bounds)


class UnmatchedParenthesesError(ParseError):
    def __init__(self, /, *, bounds: Bounds):
        super(UnmatchedParenthesesError, self).__init__(f"unmatched '('", bounds)


class DuplicateVariableError(ParseError):
    def __init__(self, /, *, word: WithBounds[str]):
        super(DuplicateVariableError, self).__init__(f"duplicate variable '{word.val}'", word.bounds)


class TrailingLambdaNotParenthesizedError(ParseError):
    def __init__(self, /, *, bounds: Bounds):
        super(TrailingLambdaNotParenthesizedError, self).__init__(f"trailing lambda must be parenthesized", bounds)


class ExternalVariableTypeError(ValueError):
    ...
