from typing import final, TypeGuard
from abc import ABC, abstractmethod


class _Ty0(ABC):
    @abstractmethod
    def __hash__(self) -> int:
        ...

    @abstractmethod
    def __eq__(self, other: object) -> bool:
        ...

    @abstractmethod
    def __str__(self) -> str:
        ...

    @property
    @abstractmethod
    def tv(self) -> frozenset['TyVar']:
        ...


@final
class TyCon(_Ty0):
    __slots__ = "name", "args", "__tv"
    __match_args__ = "name", "args"
    _arity_table = {
        "int": (0, 0),
        "float": (0, 0),
        "bool": (0, 0),
        "unit": (0, 0),
        "->": (2, ...),
        "tuple": (2, ...),
        "array": (1, 1),
    }
    _singleton_table: dict[str, 'TyCon | None'] = {
        "int": None,
        "float": None,
        "bool": None,
        "unit": None,
    }

    def __new__(cls, name: str, *args: 'Ty0'):
        if name in cls._singleton_table:
            assert len(args) == 0
            if (o := cls._singleton_table[name]) is None:
                obj = cls._singleton_table[name] = super().__new__(cls)
                return obj
            return o
        else:
            assert len(args) >= 1
            min, max = cls._arity_table[name]
            if min is not ...:
                assert min <= len(args)
            if max is not ...:
                assert len(args) <= max
            return super().__new__(cls)

        # if args[0] in cls._singleton_table:
        #     assert len(args) == 1
        #     if cls._singleton_table[args[0]] is None:
        #         cls._singleton_table[args[0]] = super().__new__(cls)
        #     return cls._singleton_table[args[0]]
        # else:
        #     assert len(args) >= 1
        #     min, max = cls._arity_table[args[0]]
        #     if min is not ...:
        #         assert min <= len(args) - 1
        #     if max is not ...:
        #         assert len(args) - 1 <= max
        # return super().__new__(cls)

    def __init__(self, name: str, /, *args: 'Ty0'):
        self.name = name
        self.args = args
        self.__tv: frozenset['TyVar'] | None = None

    def __hash__(self):
        return hash((TyCon, self.name, self.args))

    def __eq__(self, other: object):
        match other:
            case TyCon(name, args):
                return self.name == name and self.args == args
            case _:
                return False

    def __str__(self):
        match self.name:
            case 'int' | 'float' | 'bool' | 'unit' as name:
                return name
            case '->':
                buf: list[str] = []
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

    @property
    def tv(self) -> frozenset['TyVar']:
        if self.__tv is not None:
            return self.__tv
        tv: set[TyVar] = set()
        for arg in self.args:
            tv |= arg.tv
        self.__tv = frozenset(tv)
        return self.__tv


@final
class TyVar(_Ty0):
    __slots__ = "__id", "__tv"
    _counter = 0

    def __init__(self):
        self.__id = TyVar._counter
        self.__tv = frozenset({self})
        TyVar._counter += 1

    def __hash__(self):
        return hash((TyVar, self.__id))

    def __eq__(self, other: object):
        if not isinstance(other, TyVar):
            return NotImplemented
        if self is other:
            return True
        return self.__id == other.__id

    def __str__(self):
        return f"'{self.__id}"

    __repr__ = __str__

    @property
    def tv(self) -> frozenset['TyVar']:
        return self.__tv


Ty0 = TyVar | TyCon


def ty0_fun(t1: Ty0, t2: Ty0, /, *ts: Ty0) -> TyCon:
    return TyCon("->", t1, t2, *ts)


ty0_int = TyCon("int")
ty0_float = TyCon("float")
ty0_bool = TyCon("bool")
ty0_unit = TyCon("unit")


def ty0_tuple(t1: Ty0, t2: Ty0, /, *ts: Ty0) -> TyCon:
    return TyCon("tuple", t1, t2, *ts)


def ty0_array(t: Ty0, /) -> TyCon:
    return TyCon("array", t)


if __name__ == '__main__':
    print(ty0_fun(ty0_int, ty0_bool, ty0_int))
    print(ty0_tuple(ty0_int, ty0_fun(ty0_int, ty0_unit), ty0_int))


def is_ty0(x: object, /) -> TypeGuard[Ty0]:
    return isinstance(x, (TyVar, TyCon))
