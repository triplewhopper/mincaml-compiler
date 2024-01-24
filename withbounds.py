from typing import TypeVar, Generic, TypeGuard, Literal, TypeAlias
from bounds import Bounds, HasBounds

T = TypeVar("T", covariant=True)


class WithBounds(Generic[T], HasBounds):
    __slots__ = 'val',

    def __init__(self, val: T, bounds: Bounds):
        super(WithBounds, self).__init__(bounds)
        self.val = val

    def __eq__(self, other: object, /):
        if isinstance(other, WithBounds):
            return self.bounds == other.bounds and other._val_eq(self.val)
        return False
    
    def _val_eq(self, other: object, /):
        return self.val == other

    def __hash__(self):
        return hash((WithBounds[T], self.val, self.bounds))

    def __repr__(self):
        return f"<wb[{self.val.__class__.__name__}] {self.val!r}@{self.bounds!r}>"


X = TypeVar("X", bool, int, float, Literal["()"])

WithBoundsLit: TypeAlias = WithBounds[X]


def is_withboundslit(x:object) -> TypeGuard[WithBounds[X]]:
    match x:
        case WithBounds(val=int()|float()|bool()|'()'):
            return True
        case _:
            return False


def is_disjoint_increasing(*args: Bounds) -> bool:
    i = iter(args)
    try:
        x = next(i)
    except StopIteration:
        return True
    while True:
        try:
            y = next(i)
            if not (x < y):
                return False
            x = y
        except StopIteration:
            return True
