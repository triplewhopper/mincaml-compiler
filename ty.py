from collections.abc import Iterable
from abc import ABC, abstractmethod
from typing import TypeVar, Generic


class Ty(ABC):

    @abstractmethod
    def __hash__(self) -> int:
        ...

    @abstractmethod
    def __eq__(self, other: object) -> bool:
        ...

    @abstractmethod
    def __repr__(self) -> str:
        ...

    @abstractmethod
    def __str__(self) -> str:
        ...


class TyUnit(Ty):
    _instance = None
    __slots__ = ()

    def __new__(cls):
        # Singleton
        if cls._instance is None:
            cls._instance = super(TyUnit, cls).__new__(cls)
        return cls._instance

    def __hash__(self):
        return hash((TyUnit, ()))

    def __eq__(self, other: object):
        return other is self

    def __str__(self):
        return "unit"

    __repr__ = __str__


class TyBool(Ty):
    _instance = None
    __slots__ = ()

    def __new__(cls):
        # Singleton
        if cls._instance is None:
            cls._instance = super(TyBool, cls).__new__(cls)
        return cls._instance

    def __hash__(self):
        return hash((TyBool, ()))

    def __eq__(self, other: object):
        return other is self

    def __str__(self):
        return "bool"

    __repr__ = __str__


class TyInt(Ty):
    _instance = None
    __slots__ = ()

    def __new__(cls):
        # Singleton
        if cls._instance is None:
            cls._instance = super(TyInt, cls).__new__(cls)
        return cls._instance

    def __hash__(self):
        return hash((TyInt, ()))

    def __eq__(self, other: object):
        return other is self

    def __str__(self):
        return "int"

    __repr__ = __str__


class TyFloat(Ty):
    _instance = None
    __slots__ = ()

    def __new__(cls):
        # Singleton
        if cls._instance is None:
            cls._instance = super(TyFloat, cls).__new__(cls)
        return cls._instance

    def __hash__(self):
        return hash((TyFloat, ()))

    def __eq__(self, other: object):
        return other is self

    def __str__(self):
        return "float"

    __repr__ = __str__


class TyTuple(Ty):
    __slots__ = '_elems',
    __match_args__ = 'elems',

    def __init__(self, elems: Iterable[Ty]):
        self._elems = tuple(elems)
        assert len(self._elems) >= 2
        assert all(isinstance(e, Ty) for e in self._elems)

    @property
    def elems(self) -> tuple[Ty, ...]:
        return self._elems

    def __hash__(self):
        return hash((TyTuple, self._elems))

    def __eq__(self, other: object):
        return isinstance(other, TyTuple) and self._elems == other._elems

    def __repr__(self):
        return f"{' * '.join('(' + str(e) + ')' if isinstance(e, (TyTuple, TyFun)) else str(e) for e in self._elems)}"

    __str__ = __repr__


class TyArray(Ty):
    __slots__ = '_elem',
    __match_args__ = 'elem',

    def __init__(self, elem: Ty):
        self._elem = elem

    @property
    def elem(self) -> Ty:
        return self._elem

    def __hash__(self):
        return hash((TyArray, self._elem))

    def __eq__(self, other: object):
        return isinstance(other, TyArray) and self._elem == other._elem

    def __repr__(self):
        if isinstance(self._elem, (TyTuple, TyFun)):
            return f"({self._elem}) array"
        return f"{self._elem} array"

    __str__ = __repr__


class TyFun(Ty):
    __slots__ = '_args', '_ret'
    __match_args__ = 'args', 'ret'

    def __init__(self, *args: Ty):
        assert len(args) >= 2
        assert all(isinstance(e, Ty) for e in args)
        self._args: tuple[Ty, ...] = args[:-1]
        self._ret = args[-1]

    @property
    def args(self) -> tuple[Ty, ...]:
        return self._args

    @property
    def ret(self) -> Ty:
        return self._ret

    def __hash__(self):
        return hash((TyFun, self._args, self._ret))

    def __eq__(self, other: object):
        return isinstance(other, TyFun) and self._args == other._args and self._ret == other._ret

    def __repr__(self):
        s: list[str] = []
        for arg in self._args:
            if isinstance(arg, TyFun):
                s.append(f"({arg})")
            else:
                s.append(str(arg))
        s.append(f"{self._ret}")
        return " -> ".join(s)

    __str__ = __repr__


ty_i = TyInt()
ty_f = TyFloat()
ty_b = TyBool()
ty_u = TyUnit()


def ty_tuple(ts: Iterable[Ty]) -> Ty:
    return TyTuple(ts)


def ty_fun(*ts: Ty) -> Ty:
    return TyFun(*ts)


T = TypeVar("T", bound=Ty, covariant=True)


class HasTypMixin(Generic[T]):
    __slots__ = ()

    def __init__(self, typ: T):
        assert isinstance(typ, Ty)
        self.typ = typ
