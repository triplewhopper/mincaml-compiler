from typing import Final
from id import Id
from ty0 import ty0_fun, ty0_bool, ty0_int, ty0_float, ty0_unit, Ty0

preludes: Final = {
    "print_newline": Id(),
    "print_char": Id(),
    "print_int": Id(),
    "print_float": Id(),
    "read_int": Id(),
    "read_float": Id(),
    "int_of_float": Id(),
    "float_of_int": Id(),
    "abs_float": Id(),
    "truncate": Id(),
    "xor": Id(),
    "not": Id(),
    "fneg": Id(),
    "fispos": Id(),
    "fisneg": Id(),
    "fiszero": Id(),
    "fless": Id(),
    "fequal": Id(),
    "fhalf": Id(),
    "fsqr": Id(),
    "sqrt": Id(),
    "cos": Id(),
    "sin": Id(),
    "fabs": Id(),
    "floor": Id(),
    "atan": Id(),
}
uu: Final = ty0_fun(ty0_unit, ty0_unit)
iu: Final = ty0_fun(ty0_int, ty0_unit)
ui: Final = ty0_fun(ty0_unit, ty0_int)
ff: Final = ty0_fun(ty0_float, ty0_float)
fb: Final = ty0_fun(ty0_float, ty0_bool)
ffb: Final = ty0_fun(ty0_float, ty0_float, ty0_bool)

prelude_ty0s: Final[dict[Id, Ty0]] = {preludes[k]: v for k, v in {
    "print_newline": uu,
    "print_char": iu,
    "print_int": iu,
    "print_float": ty0_fun(ty0_float, ty0_unit),
    "read_int": ui,
    "read_float": ty0_fun(ty0_unit, ty0_float),
    "int_of_float": ty0_fun(ty0_float, ty0_int),
    "float_of_int": ty0_fun(ty0_int, ty0_float),
    "abs_float": ff,
    "truncate": ty0_fun(ty0_float, ty0_int),
    "xor": ty0_fun(ty0_bool, ty0_bool, ty0_bool),
    "not": ty0_fun(ty0_bool, ty0_bool),
    "fneg": ff,
    "fispos": fb,
    "fisneg": fb,
    "fiszero": fb,
    "fless": ffb,
    "fequal": ffb,
    "fhalf": ff,
    "fsqr": ff,
    "sqrt": ff,
    "cos": ff,
    "sin": ff,
    "fabs": ff,
    "floor": ff,
    "atan": ff,
}.items()}

