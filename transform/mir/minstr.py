from transform.mir.mir import MachineOperand as MO, MachineBasicBlock as MBB
from transform.mir.reg import MachineRegister as MReg


class MachineInstr:
    ...


class Ret(MachineInstr):
    def __init__(self, value: MO):
        self.value = value

    def __repr__(self):
        return f"<ret {self.value}>"


class RetVoid(MachineInstr):
    def __repr__(self):
        return "<ret void>"


class Binary(MachineInstr):
    opcode = ''

    def __init__(self, dest: MReg, lhs: MO, rhs: MO):
        assert lhs.typ == rhs.typ == dest.typ
        self.lhs = lhs
        self.rhs = rhs
        self.dest = dest

    def __repr__(self):
        return f"<{self.dest} = {self.opcode} {self.lhs} {self.rhs}>"


class Add(Binary): opcode = "add"


class Mul(Binary): opcode = "mul"
