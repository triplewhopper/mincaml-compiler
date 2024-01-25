import os
import sys
import base64

from typing import TypeVar, Type
from abc import ABC, abstractmethod
from bounds import Bounds

T = TypeVar("T", bool, int, float)


class Tok(ABC):
    __slots__ = '_text', '_bounds'

    def __init__(self, text: str, b: Bounds):
        assert isinstance(text, str) and isinstance(b, Bounds)
        if b.lineno == b.end_lineno:
            assert b.colno + len(text) == b.end_colno
        self._text = text
        self._bounds = b

    @property
    def bounds(self) -> Bounds:
        return self._bounds

    #
    # @property
    # def bounds(self) -> tuple[int, int]:
    #     return self._loc, self._loc + len(self._text)

    @property
    def text(self) -> str:
        return self._text

    def get_val(self, ty: Type[T]) -> T:
        """ :raises ValueError: if the current token does not match the type"""
        raise NotImplementedError()

    def match(self, other: str) -> bool:
        raise NotImplementedError()

    @abstractmethod
    def is_ident(self, capitalized: bool = False) -> bool:
        raise NotImplementedError()
    
    def get_ident(self, capitalized: bool = False) -> str:
        """ :raises ValueError: if the current token is not an identifier"""
        raise ValueError(self.text)


class Val(Tok):
    __slots__ = '_val'
    __match_args__ = ('val',)

    def __init__(self, text: str, val: int | float | bool | str, b: Bounds):
        super().__init__(text, b)
        self._val = val

    def __repr__(self):
        return f"Val({repr(self._val)})"

    @property
    def val(self):
        return self._val

    def get_val(self, ty: Type[T]) -> T:
        """ :raises ValueError: if the current token does not match the type"""
        if isinstance(self._val, ty) and ty in {bool, int, float}:
            return self._val

        raise ValueError(ty)

    def match(self, other: str):
        return False

    def is_ident(self, capitalized: bool = False):
        return False


class Word(Tok):
    __match_args__ = 'text',
    __keywords = frozenset({
        'and', 'as', 'assert', 'asr', 'begin', 'class', 'constraint', 'do', 'done', 'downto', 'else', 'end',
        'exception',
        'external', 'false', 'for', 'fun', 'function', 'functor', 'if', 'in', 'include', 'inherit', 'initializer',
        'land', 'lazy', 'let', 'lor', 'lsl', 'lsr', 'lxor', 'match', 'method', 'mod', 'module', 'mutable', 'new',
        'nonrec', 'object', 'of', 'open', 'or', 'private', 'rec', 'sig', 'struct', 'then', 'to', 'true', 'try', 'type',
        'val', 'virtual', 'when', 'while', 'with'
    })

    def __init__(self, word: str, b: Bounds):
        super().__init__(word, b)

    def __repr__(self):
        return f"Word({repr(self.text)})"

    def match(self, other: str) -> bool:
        assert isinstance(other, str)
        return self.text == other

    def is_ident(self, capitalized: bool = False) -> bool:
        if self.text in self.__keywords:
            return False
        if capitalized:
            return self.text[0].isupper()
        else:
            return self.text[0].islower() or self.text.startswith('_')

    def get_ident(self, capitalized: bool = False) -> str:
        """ :raises ValueError: if the current token is a keyword or does not match the capitalization"""
        if self.text in self.__keywords:
            raise ValueError(self.text)
        if capitalized and not self.text[0].isupper():
            raise ValueError(self.text)
        if not capitalized and not (self.text[0].islower() or self.text.startswith('_')):
            raise ValueError(self.text)
        return self.text


class EOF(Tok):
    def __init__(self, b: Bounds):
        super().__init__('', b)

    def __repr__(self): return f"EOF()"

    def match(self, other: str):
        return False

    def is_ident(self, capitalized: bool = False):
        return False


def lex(filepath: str):

    if os.system(f"{os.path.dirname(__file__)}/lex {filepath}") != 0:
        raise RuntimeError("Lex failed")
    with open(f"{filepath}.lex") as f:
        for line in f:
            _, lineno, colno, end_lineno, end_colno, kind, text = line.split()
            loc = Bounds(filepath, int(lineno), int(colno), int(end_lineno), int(end_colno))
            match kind:
                case 'I':
                    yield Val(text, int(text), loc)
                case 'B':
                    yield Val(text, {'true': True, 'false': False}[text], loc)
                case 'F':
                    yield Val(text, float(text), loc)
                case 'S':
                    s = base64.b64decode(text).decode()
                    yield Val(s, s, loc)
                case 'Op' | 'W':
                    yield Word(text, loc)
                case 'EOF':
                    yield EOF(loc)
                case 'E':
                    e = base64.b64decode(text).decode()
                    print(e, file=sys.stderr)
                    exit(1)
                case _:
                    raise ValueError(f"Unknown token kind: {kind}")


if __name__ == "__main__":
    for token in lex("samples/fib.ml"):
        print(repr(token))
