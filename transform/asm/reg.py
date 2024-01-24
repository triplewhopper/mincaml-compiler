from enum import Enum, auto
from abc import ABC, abstractmethod
from typing import Literal


class Register(Enum):
    x0 = 0
    x1 = 1
    x2 = 2
    x3 = 3
    x4 = 4
    x5 = 5
    x6 = 6
    x7 = 7
    x8 = 8
    x9 = 9
    x10 = 10
    x11 = 11
    x12 = 12
    x13 = 13
    x14 = 14
    x15 = 15
    x16 = 16
    x17 = 17
    x18 = 18
    x19 = 19
    x20 = 20
    x21 = 21
    x22 = 22
    x23 = 23
    x24 = 24
    x25 = 25
    x26 = 26
    x27 = 27
    x28 = 28
    x29 = 29
    x30 = 30
    x31 = 31
    f0 = 32
    f1 = 33
    f2 = 34
    f3 = 35
    f4 = 36
    f5 = 37
    f6 = 38
    f7 = 39
    f8 = 40
    f9 = 41
    f10 = 42
    f11 = 43
    f12 = 44
    f13 = 45
    f14 = 46
    f15 = 47
    f16 = 48
    f17 = 49
    f18 = 50
    f19 = 51
    f20 = 52
    f21 = 53
    f22 = 54
    f23 = 55
    f24 = 56
    f25 = 57
    f26 = 58
    f27 = 59
    f28 = 60
    f29 = 61
    f30 = 62
    f31 = 63

    def __int__(self):
        return self.value & 31


class ABIName(ABC):
    def __eq__(self, other):
        if isinstance(other, ABIName):
            return self.reg == other.reg
        return NotImplemented

    def __hash__(self):
        return hash(self.reg)

    @property
    def reg(self) -> Register:
        raise NotImplementedError()

    def __int__(self):
        return int(self.reg)


class Zero(ABIName):
    """Hardwired zero"""

    def __str__(self):
        return "<zero>"

    @property
    def reg(self) -> Literal[Register.x0]:
        return Register.x0


class CallerSaved(ABIName):
    ...


class CalleeSaved(ABIName):
    ...


class Ra(CallerSaved):
    """Return address"""

    def __str__(self):
        return "<ra>"

    @property
    def reg(self) -> Literal[Register.x1]:
        return Register.x1


class Sp(CalleeSaved):
    """Stack pointer"""

    def __str__(self):
        return "<sp>"

    @property
    def reg(self) -> Literal[Register.x2]:
        return Register.x2


class Gp(ABIName):
    """Global pointer"""

    def __str__(self):
        return "<gp>"

    @property
    def reg(self) -> Literal[Register.x3]:
        return Register.x3


class Tp(ABIName):
    """Thread pointer"""

    def __str__(self):
        return "<tp>"

    @property
    def reg(self) -> Literal[Register.x4]:
        return Register.x4


class T(CallerSaved):
    """
    t0-2: Temporaries
    t3-6: Temporaries
    """
    __match_args__ = ("_i",)

    def __init__(self, i: int):
        assert i in (0, 1, 2, 3, 4, 5, 6)
        self._i = i

    def __str__(self):
        return f"<t{self._i}>"

    @property
    def reg(self) -> Register:
        return (
            Register.x5, Register.x6, Register.x7,
            Register.x28, Register.x29, Register.x30,
            Register.x31)[self._i]


class S(CalleeSaved):
    """
    s0/fp: Saved register/frame pointer
    s1: Saved register
    s2-11:Saved registers
    """
    __match_args__ = ("_i",)

    def __init__(self, i: int):
        assert i in (0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11)
        self._i = i

    def __str__(self):
        return f"<s{self._i}>"

    @property
    def reg(self) -> Register:
        return (
            Register.x8, Register.x9, Register.x18, Register.x19,
            Register.x20, Register.x21, Register.x22,
            Register.x23, Register.x24, Register.x25,
            Register.x26, Register.x27)[self._i]


class Fp(CalleeSaved):
    """
    s0/fp: Saved register/frame pointer
    """

    def __str__(self):
        return "<fp>"

    @property
    def reg(self) -> Literal[Register.x8]:
        return Register.x8


class A(CallerSaved):
    """
    a0-1: Function arguments/return values
    a2-7: Function arguments
    """
    __match_args__ = ("_i",)

    def __init__(self, i: int):
        assert i in (0, 1, 2, 3, 4, 5, 6, 7)
        self._i = i

    def __str__(self):
        return f"<a{self._i}>"

    @property
    def reg(self) -> Register:
        return (
            Register.x10, Register.x11, Register.x12, Register.x13,
            Register.x14, Register.x15, Register.x16, Register.x17)[self._i]


class Ft(CallerSaved):
    """
    ft0-7: FP temporaries
    ft8-11: FP temporaries
    """
    __match_args__ = ("_i",)

    def __init__(self, i: int):
        assert isinstance(i, int) and 0 <= i <= 11
        self._i = i

    def __str__(self):
        return f"<ft{self._i}>"

    @property
    def reg(self) -> Register:
        return (
            Register.f0, Register.f1, Register.f2, Register.f3,
            Register.f4, Register.f5, Register.f6, Register.f7,
            Register.f28, Register.f29, Register.f30, Register.f31)[self._i]


class Fa(CallerSaved):
    """
    fa0-1: FP arguments/return values
    fa2-7: FP arguments
    """
    __match_args__ = ("_i",)

    def __init__(self, i: int):
        assert i in (0, 1, 2, 3, 4, 5, 6, 7)
        self._i = i

    def __str__(self):
        return f"<fa{self._i}>"

    @property
    def reg(self) -> Register:
        return (
            Register.f10, Register.f11, Register.f12, Register.f13,
            Register.f14, Register.f15, Register.f16, Register.f17)[self._i]


class Fs(CalleeSaved):
    """
    fs0-1: FP saved registers
    fs2-11: FP saved registers
    """
    __match_args__ = ("_i",)

    def __init__(self, i: int):
        assert i in (0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11)
        self._i = i

    def __str__(self):
        return f"<fs{self._i}>"

    @property
    def reg(self) -> Register:
        return (
            Register.f8, Register.f9, Register.f18, Register.f19,
            Register.f20, Register.f21, Register.f22,
            Register.f23, Register.f24, Register.f25,
            Register.f26, Register.f27)[self._i]
