from virtual.virtual import Value, Function, BasicBlock, PreludeTy
from virtual.virtual import GetElementPtr, Ret, RetVoid, get_abi_size
from transform.mir.mir import MachineFunction, MachineBasicBlock as MBB, MachineOperand as MO

from transform.mir.reg import VirtualRegister as VReg, VirtualTmpRegister as VTmpReg
from transform.mir.minstr import (
    MachineInstr,
    Ret as MachineRet,
    RetVoid as MachineRetVoid,
    Add as MachineAdd,
    Mul as MachineMul, )


def translate(self: Function) -> MachineFunction:
    env = list(self.args)
    env2 = [MO(VReg(arg.rd, arg.typ)) for arg in self.args]
    mf = MachineFunction()
    for bb in self.blocks:
        bb.translate(mf, env, env2)


def translate(self: BasicBlock, mf: MachineFunction, env: list[Value], env2: list[MO]) -> MBB:
    def to_mv(v: Value) -> MO:
        return env2[env.index(v)]

    assert len(env) == len(env2)
    mbb = MBB(mf)
    mf.blocks.append(mbb)
    i = 0
    while i < len(self.instructions):
        instr = self.instructions[i]
        if isinstance(instr, Ret):
            mbb.instructions.append(MachineRet(to_mv(instr.rs)))
        elif isinstance(instr, GetElementPtr) and
            mul = MachineMul(VTmpReg(), to_mv(i), MO(get_abi_size(t)))
            add = MachineAdd(VTmpReg(), to_mv(instr.rs), MO(mul.dest))
            mbb.instructions.append(mul)
            mbb.instructions.append(add)

            for i, t in zip(instr.indices, instr.gep_typs):
                mul = MachineMul(VTmpReg(), to_mv(i), MO(get_abi_size(t)))
                add = MachineAdd(VTmpReg(), MO(add.dest), MO(mul.dest))
                mbb.instructions.append(mul)
                mbb.instructions.append(add)

            add.dest = VReg(instr.rd, instr.typ)
