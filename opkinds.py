from enum import Enum, auto, unique
import functools
from typing import Literal
from ty import TyFun, TyBool, TyInt, TyFloat

binary_operators = {'+', '+.', '-', '-.', '*', '*.', '/', '/.', '<', '<=', '>', '>=', '=', '<>', 'lsl', 'asr', 'land', 'lor', 'lxor'}
literal_binary = Literal['+', '+.', '-', '-.', '*', '*.', '/', '/.', '<', '<=', '>', '>=', '=', '<>', 'lsl', 'asr', 'land', 'lor', 'lxor']
unary_operators = ('-', '-.')
literal_unary = Literal['-', '-.']


@unique
class UnaryOpKind(Enum):
    I_NEG = auto()
    F_NEG = auto()

    @property
    @functools.lru_cache
    def typ(self):
        match self:
            case UnaryOpKind.I_NEG:
                return TyFun(TyInt(), TyInt())
            case UnaryOpKind.F_NEG:
                return TyFun(TyFloat(), TyFloat())

    def __str__(self) -> literal_unary:
        match self:
            case UnaryOpKind.I_NEG:
                return "-"
            case UnaryOpKind.F_NEG:
                return "-."


@unique
class BinaryOpKind(Enum):
    I_ADD = auto()
    I_SUB = auto()
    I_MUL = auto()
    I_DIV = auto()

    I_SHL = auto()
    I_SHR = auto()

    I_AND = auto()
    I_OR = auto()
    I_XOR = auto()

    F_ADD = auto()
    F_SUB = auto()
    F_MUL = auto()
    F_DIV = auto()

    I_LT = auto()
    F_LT = auto()

    I_LE = auto()
    F_LE = auto()

    I_EQ = auto()
    F_EQ = auto()
    B_EQ = auto()

    I_NEQ = auto()
    F_NEQ = auto()
    B_NEQ = auto()

    I_GE = auto()
    F_GE = auto()

    I_GT = auto()
    F_GT = auto()

    @property
    @functools.lru_cache
    def typ(self):
        match self:
            case BinaryOpKind.I_ADD | BinaryOpKind.I_SUB | BinaryOpKind.I_MUL | BinaryOpKind.I_DIV | BinaryOpKind.I_SHL | BinaryOpKind.I_SHR | BinaryOpKind.I_AND | BinaryOpKind.I_OR | BinaryOpKind.I_XOR:
                return TyFun(TyInt(), TyInt(), TyInt())
            case BinaryOpKind.I_LT | BinaryOpKind.I_LE | BinaryOpKind.I_EQ | BinaryOpKind.I_NEQ | BinaryOpKind.I_GE | BinaryOpKind.I_GT:
                return TyFun(TyInt(), TyInt(), TyBool())
            case BinaryOpKind.F_ADD | BinaryOpKind.F_SUB | BinaryOpKind.F_MUL | BinaryOpKind.F_DIV:
                return TyFun(TyFloat(), TyFloat(), TyFloat())
            case BinaryOpKind.F_LT | BinaryOpKind.F_LE | BinaryOpKind.F_EQ | BinaryOpKind.F_NEQ | BinaryOpKind.F_GE | BinaryOpKind.F_GT:
                return TyFun(TyFloat(), TyFloat(), TyBool())
            case BinaryOpKind.B_EQ | BinaryOpKind.B_NEQ:
                return TyFun(TyBool(), TyBool(), TyBool())

    def __str__(self) -> literal_binary:
        match self:
            case BinaryOpKind.I_ADD:
                return "+"
            case BinaryOpKind.I_SUB:
                return "-"
            case BinaryOpKind.I_MUL:
                return "*"
            case BinaryOpKind.I_DIV:
                return "/"
            case BinaryOpKind.I_SHL:
                return "lsl"
            case BinaryOpKind.I_SHR:
                return "asr"
            case BinaryOpKind.I_AND:
                return "land"
            case BinaryOpKind.I_OR:
                return "lor"
            case BinaryOpKind.I_XOR:
                return "lxor"
            case BinaryOpKind.F_ADD:
                return "+."
            case BinaryOpKind.F_SUB:
                return "-."
            case BinaryOpKind.F_MUL:
                return "*."
            case BinaryOpKind.F_DIV:
                return "/."
            case BinaryOpKind.I_LT | BinaryOpKind.F_LT:
                return "<"
            case BinaryOpKind.I_LE | BinaryOpKind.F_LE:
                return "<="
            case BinaryOpKind.I_EQ | BinaryOpKind.F_EQ | BinaryOpKind.B_EQ:
                return "="
            case BinaryOpKind.I_NEQ | BinaryOpKind.F_NEQ | BinaryOpKind.B_NEQ:
                return "<>"
            case BinaryOpKind.I_GE | BinaryOpKind.F_GE:
                return ">="
            case BinaryOpKind.I_GT | BinaryOpKind.F_GT:
                return ">"
