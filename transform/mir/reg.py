from id import Id
from llvmlite.ir import Type, IntType, FloatType

i32 = IntType(32)
f32 = FloatType()


class MachineRegister:
    _id = 0
    typ: Type

    def __eq__(self, other):
        raise NotImplementedError()


class PhysicalRegister(MachineRegister):
    def __init__(self, x: int):
        assert 0 <= x <= 63
        self._x = x
        self.typ = i32 if x <= 31 else f32
        self.name = None

    def __eq__(self, other):
        if isinstance(other, PhysicalRegister):
            return self._x == other._x
        elif isinstance(other, VirtualRegister):
            return False
        return NotImplemented

    def __hash__(self):
        return hash((PhysicalRegister, self._x))

    def __repr__(self):
        return f'<phy:{self._x}>' if self.name is None else f'<phy:{self._x}:{self.name}>'

    def __str__(self):
        if 0 <= self._x <= 31:
            return f"$x{self._x}"
        else:
            return f"$f{self._x - 32}"


class VirtualRegister(MachineRegister):
    _counter = 0

    def __init__(self, name: Id, typ: Type):
        self.name = name
        self._id = VirtualRegister._counter
        VirtualRegister._counter += 1
        self.typ = typ

    def __eq__(self, other):
        if isinstance(other, VirtualRegister):
            return self._id == other._id
        elif isinstance(other, PhysicalRegister):
            return False
        return NotImplemented

    def __hash__(self):
        return hash((VirtualRegister, self._id))

    def __repr__(self):
        return f'<vt:{self._id}:{self.name}:{self.typ}>'


class VirtualTmpRegister(VirtualRegister):
    def __init__(self, typ: Type = i32):
        self.name = None
        self._id = VirtualRegister._counter
        VirtualRegister._counter += 1
        self.typ = typ

    def __repr__(self):
        return f'<vt:{self._id}:{self.typ}>'
