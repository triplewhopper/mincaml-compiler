import enum
import functools
from typing import Literal
from ty import TyFun, TyBool, TyInt, TyFloat

binary_operators = {'+', '+.', '-', '-.', '*', '*.', '/', '/.', '<', '<=', '>', '>=', '=', '<>'}
literal_binary = Literal['+', '+.', '-', '-.', '*', '*.', '/', '/.', '<', '<=', '>', '>=', '=', '<>']
unary_operators = ('-', '-.')
literal_unary = Literal['-', '-.']


@enum.unique
class UnaryOpKind(enum.Enum):
    I_NEG = 1
    F_NEG = 2

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


@enum.unique
class BinaryOpKind(enum.Enum):
    I_ADD = 1
    I_SUB = 2
    I_MUL = 3
    I_DIV = 4

    F_ADD = 5
    F_SUB = 6
    F_MUL = 8
    F_DIV = 9

    I_LT = 10
    F_LT = 11

    I_LE = 12
    F_LE = 13

    I_EQ = 14
    F_EQ = 15
    B_EQ = 16

    I_NEQ = 17
    F_NEQ = 18
    B_NEQ = 19

    I_GE = 20
    F_GE = 21

    I_GT = 22
    F_GT = 23

    @property
    @functools.lru_cache
    def typ(self):
        match self:
            case BinaryOpKind.I_ADD | BinaryOpKind.I_SUB | BinaryOpKind.I_MUL | BinaryOpKind.I_DIV:
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
