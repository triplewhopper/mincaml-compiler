from dataclasses import dataclass
from collections.abc import Sequence
from transform.closure.basictype import BasicType


@dataclass
class ValueType:
    @property
    def abi_size(self) -> int:
        """The size in words of the type in the ABI"""
        raise NotImplementedError()

    def base(self) -> 'ValueType':
        raise NotImplementedError()
    
    def tchar(self) -> str:
        raise NotImplementedError()
    
    def to_basic_types(self) -> Sequence[BasicType]:
        raise NotImplementedError()


@dataclass
class IntType(ValueType):
    @property
    def abi_size(self):
        return 1

    def base(self) -> 'IntType':
        return self

    def __repr__(self) -> str:
        return 'int'
    
    def tchar(self):
        return 'i'
    
    def to_basic_types(self):
        return BasicType.T_INT,


@dataclass
class FloatType(ValueType):
    @property
    def abi_size(self):
        return 1

    def base(self) -> 'FloatType':
        return self

    def __repr__(self) -> str:
        return 'float'
    
    def tchar(self):
        return 'f'
    
    def to_basic_types(self):
        return BasicType.T_FLOAT,


@dataclass
class ArrayType(ValueType):
    elem: ValueType

    @property
    def abi_size(self):
        return 1

    def base(self):
        return ArrayType(self.elem.base())

    def __repr__(self):
        return f'{self.elem}[]'
    
    def tchar(self):
        return 'a'
    
    def to_basic_types(self):
        return BasicType.T_INT,


@dataclass
class IntConstant(IntType):
    value: int

    def base(self):
        return IntType()

    def __repr__(self):
        return f"int<{self.value}>"


@dataclass
class FloatConstant(FloatType):
    value: float

    def base(self):
        return FloatType()

    def __repr__(self):
        return f"float<{self.value}>"

@dataclass
class ClosureType(ValueType):
    formal_args: tuple[ValueType, ...]
    ret: ValueType | None

    @property
    def abi_size(self):
        return 2

    def base(self):
        args = tuple(x.base() for x in self.formal_args)
        ret = self.ret.base() if self.ret is not None else None
        return ClosureType(args, ret)

    def __repr__(self):
        return f"{self.ret}({', '.join(map(str, self.formal_args))})"
    
    def tchar(self):
        return 'c'
    
    def to_basic_types(self):
        return BasicType.T_INT, BasicType.T_INT


@dataclass
class TupleType(ValueType):
    elems: tuple[ValueType, ...]

    @property
    def abi_size(self):
        return sum(x.abi_size for x in self.elems)

    def base(self):
        return TupleType(tuple(x.base() for x in self.elems))

    def __repr__(self):
        return f"({', '.join(map(str, self.elems))})"
    
    def tchar(self):
        return 'w'
    
    def to_basic_types(self):
        return sum((tuple(x.to_basic_types()) for x in self.elems), ())
