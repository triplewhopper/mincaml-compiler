from typing import TypeVar, Generic, Tuple
from pyparsing import lineno, col

T = TypeVar("T")


class WithBounds(Generic[T]):
    __slots__ = ["_val", "_bounds"]

    def __init__(self, val: T, bounds: Tuple[int, int]):
        self._val = val
        self._bounds = bounds

    @property
    def val(self) -> T:
        return self._val

    @property
    def bounds(self) -> Tuple[int, int]:
        return self._bounds

    def lineno(self, s: bytes) -> int | Tuple[int, int]:
        p = s.count(b'\n', 0, self._bounds[0]) + 1
        q = s.count(b'\n', 0, self._bounds[1]) + 1
        return p if p == q else (p, q)

    def col(self, s: bytes) -> int | Tuple[int, int]:
        p = [1 if 0 < loc < len(s) and s[loc - 1] == b'\n' else loc - s.rfind(b'\n', 0, loc) for loc in self._bounds]
        return p[0] if p[0] == p[1] else p

    def __hash__(self):
        return hash((self._val, self._bounds))

    def __eq__(self, other):
        if not isinstance(other, WithBounds):
            return NotImplemented
        return self._val == other._val and self._bounds == other._bounds

    def __repr__(self):
        return f"WithBounds({self._val!r}, {self._bounds!r})"


def merge(b1: tuple[int, int], *bs: tuple[int, int]) -> tuple[int, int]:
    return min(b1[0], *map(lambda x: x[0], bs)), \
           max(b1[1], *map(lambda x: x[1], bs))
