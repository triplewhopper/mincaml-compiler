import os
import sys
import base64

from typing import TypeVar, Type, overload
from abc import ABC, abstractmethod

T = TypeVar("T")


class Loc:
    def __init__(self, loc: int):
        self._loc = loc

    @property
    def loc(self) -> int:
        return self._loc


class Tok(ABC, Loc):
    def __init__(self, loc: int, text: str):
        super().__init__(loc)
        self._text = text

    @property
    def loc(self) -> int:
        return self._loc

    @property
    def bounds(self) -> tuple[int, int]:
        return self._loc, self._loc + len(self._text)

    @property
    def text(self) -> str:
        return self._text

    @overload
    def get_val(self, ty: Type[int]) -> int:
        ...

    @overload
    def get_val(self, ty: Type[float]) -> float:
        ...

    @overload
    def get_val(self, ty: Type[bool]) -> bool:
        ...

    def get_val(self, ty: Type[T]) -> T:
        """ :raises ValueError: if the current token does not match the type"""
        raise NotImplementedError()

    def match(self, other: str) -> bool:
        raise NotImplementedError()

    @abstractmethod
    def is_ident(self, capitalized: bool = False) -> bool:
        raise NotImplementedError()


class Val(Tok):
    __match_args__ = ('val',)

    def __init__(self, loc: int, text: str, val):
        super().__init__(loc, text)
        self._val = val

    def __repr__(self):
        return f"Val({repr(self._val)})"

    @property
    def val(self):
        return self._val

    def get_val(self, ty):
        """ :raises ValueError: if the current token does not match the type"""
        if ty is bool and isinstance(self._val, bool):
            return self._val
        if ty is int and isinstance(self._val, int):
            return self._val
        if ty is float and isinstance(self._val, float):
            return self._val
        raise ValueError(ty)

    def match(self, other) -> bool:
        return False

    def is_ident(self, capitalized: bool = False) -> bool:
        return False


class Word(Tok):
    __match_args__ = ('text',)
    __keywords = {
        'and', 'as', 'assert', 'asr', 'begin', 'class', 'constraint', 'do', 'done', 'downto', 'else', 'end',
        'exception',
        'external', 'false', 'for', 'fun', 'function', 'functor', 'if', 'in', 'include', 'inherit', 'initializer',
        'land', 'lazy', 'let', 'lor', 'lsl', 'lsr', 'lxor', 'match', 'method', 'mod', 'module', 'mutable', 'new',
        'nonrec', 'object', 'of', 'open', 'or', 'private', 'rec', 'sig', 'struct', 'then', 'to', 'true', 'try', 'type',
        'val', 'virtual', 'when', 'while', 'with'
    }

    def __init__(self, loc: int, word: str):
        super().__init__(loc, word)

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
            raise ValueError()
        if capitalized and not self.text[0].isupper():
            raise ValueError()
        if not capitalized and not (self.text[0].islower() or self.text.startswith('_')):
            raise ValueError()
        return self.text


class EOF(Tok):
    def __init__(self, loc: int):
        super().__init__(loc, '')

    def __repr__(self): return f"EOF()"

    def match(self, other: str) -> bool:
        return False

    def is_ident(self, capitalized: bool = False) -> bool:
        return False


def lex(filename: str):
    if os.system(f"./lex {filename} > {filename}.lex"):
        raise RuntimeError("Lex failed")
    with open(f"{filename}.lex") as f:
        for line in f:
            loc, kind, val = line.split()
            loc = int(loc)
            match kind:
                case 'I':
                    yield Val(loc, val, int(val))
                case 'B':
                    yield Val(loc, val, {'true': True, 'false': False}[val])
                case 'F':
                    yield Val(loc, val, float(val))
                case 'S':
                    s = base64.b64decode(val).decode()
                    yield Val(loc, s, s)
                case 'Op' | 'W':
                    yield Word(loc, val)
                case 'EOF':
                    yield EOF(loc)
                case 'E':
                    e = base64.b64decode(val).decode()
                    print(e, file=sys.stderr)
                    exit(1)
                case _:
                    raise ValueError(f"Unknown token kind: {kind}")


if __name__ == "__main__":
    for token in lex("samples/fib.ml"):
        print(repr(token))
