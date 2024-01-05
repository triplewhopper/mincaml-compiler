from typing import Iterable, FrozenSet
from abc import ABC, abstractmethod


class Ty0(ABC):
    @abstractmethod
    def __hash__(self):
        ...

    @abstractmethod
    def __eq__(self, other: 'Ty0'):
        ...

    @abstractmethod
    def __str__(self):
        ...

    @abstractmethod
    def accept(self, visitor: 'Ty0Visitor'):
        ...

    @property
    @abstractmethod
    def tv(self) -> FrozenSet['TyVar']:
        ...


class TyCon(Ty0):
    __slots__ = ["name", "args", "__tv"]
    __match_args__ = ("name", "args")
    _arity_table = {
        "int": (0, 0),
        "float": (0, 0),
        "bool": (0, 0),
        "unit": (0, 0),
        "->": (2, ...),
        "tuple": (2, ...),
        "array": (1, 1),
    }
    _singleton_table = {
        "int": None,
        "float": None,
        "bool": None,
        "unit": None,
    }

    def __new__(cls, *args, **kwargs):
        if args[0] in cls._singleton_table:
            assert len(args) == 1
            if cls._singleton_table[args[0]] is None:
                cls._singleton_table[args[0]] = super().__new__(cls)
            return cls._singleton_table[args[0]]
        else:
            assert len(args) >= 1
            min, max = cls._arity_table[args[0]]
            if min is not ...:
                assert min <= len(args) - 1
            if max is not ...:
                assert len(args) - 1 <= max
        return super().__new__(cls)

    def __init__(self, name: str, *args: 'Ty0'):
        self.name = name
        self.args = args
        self.__tv = None

    def __hash__(self):
        return hash((TyCon, self.name, self.args))

    def __eq__(self, other: Ty0):
        match other:
            case TyCon(name, args):
                return self.name == name and self.args == args
            case TyVar():
                return False
            case _:
                return NotImplemented

    def __str__(self):
        match self.name:
            case 'int' | 'float' | 'bool' | 'unit' as name:
                return name
            case '->':
                buf = []
                for arg in self.args[:-1]:
                    match arg:
                        case TyCon('tuple', _) | TyCon('->', _):
                            buf.append(f"({arg})")
                        case _:
                            buf.append(str(arg))
                buf.append(str(self.args[-1]))
                return " -> ".join(buf)
            case 'tuple':
                buf = []
                for arg in self.args:
                    match arg:
                        case TyCon('tuple', _) | TyCon('->', _):
                            buf.append(f"({arg})")
                        case _:
                            buf.append(str(arg))
                return " * ".join(buf)
            case 'array':
                match self.args[0]:
                    case TyCon('tuple', _) | TyCon('->', _):
                        return f"({self.args[0]}) array"
                    case _:
                        return f"{self.args[0]} array"
            case _:
                raise NotImplementedError()

    __repr__ = __str__

    def accept(self, visitor: 'Ty0Visitor'):
        return visitor.visit_tycon(self)

    @property
    def tv(self) -> FrozenSet['TyVar']:
        if self.__tv is not None:
            return self.__tv
        tv = set()
        for arg in self.args:
            tv |= arg.tv
        self.__tv = frozenset(tv)
        return self.__tv


class TyVar(Ty0):
    __slots__ = ["__id", "__tv"]
    _counter = 0

    def __init__(self):
        self.__id = TyVar._counter
        self.__tv = frozenset({self})
        TyVar._counter += 1

    def __hash__(self):
        return hash((TyVar, self.__id))

    def __eq__(self, other: Ty0):
        if not isinstance(other, TyVar):
            return NotImplemented
        if self is other:
            return True
        return isinstance(other, TyVar) and self.__id == other.__id

    def __str__(self):
        return f"'{self.__id}"

    __repr__ = __str__

    def accept(self, visitor: 'Ty0Visitor'):
        return visitor.visit_tyvar(self)

    @property
    def tv(self) -> FrozenSet['TyVar']:
        return self.__tv


def ty0_fun(t1: Ty0, t2: Ty0, *ts: Ty0) -> TyCon:
    ts = [t1, t2, *ts]
    return TyCon("->", *ts)


ty0_int = TyCon("int")
ty0_float = TyCon("float")
ty0_bool = TyCon("bool")
ty0_unit = TyCon("unit")


def ty0_tuple(t1: Ty0, t2: Ty0, *ts: Ty0) -> TyCon:
    return TyCon("tuple", t1, t2, *ts)


def ty0_array(t: Ty0) -> TyCon:
    return TyCon("array", t)


class Ty0Visitor(ABC):

    def visit(self, ty: Ty0):
        return ty.accept(self)

    @abstractmethod
    def visit_tycon(self, tycon: TyCon):
        ...

    @abstractmethod
    def visit_tyvar(self, tyvar: TyVar):
        ...


if __name__ == '__main__':
    print(ty0_fun(ty0_int, ty0_bool, ty0_int))
    print(ty0_tuple(ty0_int, ty0_fun(ty0_int, ty0_unit), ty0_int))
