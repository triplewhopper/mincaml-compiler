from transform.mir.minstr import MachineInstr
from transform.mir.reg import MachineRegister
from llvmlite.ir import Type, IntType, FloatType

i32 = IntType(32)
f32 = FloatType()


class MachineOperand:
    def __init__(self, v: int | float | MachineRegister | 'MachineBasicBlock'):
        match v:
            case int():
                self.value = int(v)
                self.typ = i32
            case float():
                self.value = float(v)
                self.typ = f32
            case MachineRegister():
                self.value = v
                self.typ = v.typ
            case MachineBasicBlock():
                self.value = v
                self.typ = i32.as_pointer()
            case _:
                raise TypeError(v)

    def __str__(self):
        return str(self.value)

    def __repr__(self):
        return str(self)

    def __eq__(self, other):
        return self.value == other.value

    def __hash__(self):
        return hash(self.value)


class MachineBasicBlock:
    def __init__(self, parent: 'MachineFunction'):
        super().__init__(self)
        self.instructions: list[MachineInstr] = []
        self.predecessors: list[MachineBasicBlock] = []
        self.successors: list[MachineBasicBlock] = []
        self.parent: MachineFunction = parent


class MachineFunction:
    def __init__(self):
        self.blocks: list[MachineBasicBlock] = []
