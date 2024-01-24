from transform.asm.reg import ABIName
from collections import namedtuple
from typing import Any

triple = namedtuple("triple", "opcode funct3 funct7")


class Asm:
    opcode = ''


#
# class OpCode(Enum):
#     ADD = triple(51, 0x0, 0)
#     SUB = triple(51, 0x0, 0x20)
#     XOR = triple(51, 0x4, 0)
#     OR = triple(51, 0x6, 0)
#     AND = triple(51, 0x7, 0)
#     SLL = triple(51, 0x1, 0)
#     SRL = triple(51, 0x5, 0)
#     SRA = triple(51, 0x5, 0x20)
#     SLT = triple(51, 0x2, 0)
#     SLTU = triple(51, 0x3, 0x00)
#
#     ADDI = triple(19, 0x0, None)
#     XORI = triple(19, 0x4, None)
#     ORI = triple(19, 0x6, None)
#     ANDI = triple(19, 0x7, None)
#     SLLI = triple(19, 0x1, None)
#     SRLI = triple(19, 0x5, None)
#     SRAI = triple(19, 0x5, None)
#     SLTI = triple(19, 0x2, None)
#     SLTIU = triple(19, 0x3, None)
#
#     LW = triple(3, 0x2, None)
#     SW = triple(35, 0x2, None)
#
#     BEQ = triple(99, 0x0, None)
#     BNE = triple(99, 0x1, None)
#     BLT = triple(99, 0x4, None)
#     BGE = triple(99, 0x5, None)
#     BLTU = triple(99, 0x6, None)
#     BGEU = triple(99, 0x7, None)
#
#     JAL = triple(111, None, None)
#     JALR = triple(103, 0x0, None)
#
#     LUI = triple(55, None, None)
#     AUIPC = triple(23, None, None)
#
#     FLW = triple(7, 0x2, None)
#     FSW = triple(39, 0x2, None)
#
#     FMADDS = triple(51, 0x0, 0x50)
#     FMSUB = triple(71, 0x0, 0x50)


class Rs2Disabled:
    def __set__(self, instance: Any, value: Any):
        raise AttributeError("rs2 disabled")

    def __get__(self, instance: Any, owner: Any):
        raise AttributeError("rs2 disabled")


class R(Asm):
    def __init__(self, rd, rs1, rs2):
        self.rd = rd
        self.rs1 = rs1
        self.rs2 = rs2

    def __repr__(self) -> str:
        assert self.opcode != ''
        return f"<{self.opcode} {self.rd}, {self.rs1}, {self.rs2}>"


class R4(Asm):
    def __init__(self, fd, fs1, fs2, fs3):
        self.fd, self.fs1, self.fs2, self.fs3 = fd, fs1, fs2, fs3

    def __repr__(self) -> str:
        assert self.opcode != ''
        return f"<{self.opcode} {self.fd}, {self.fs1}, {self.fs2}, {self.fs3}>"


#
# def pack_R(opcode: int, funct3: int, funct7: int, rd: int, rs1: int, rs2: int):
#     return struct.pack("<I", opcode | rd << 7 | funct3 << 12 | rs1 << 15 | rs2 << 20 | funct7 << 25)
#
#
# def pack_R4(opcode: int, funct2: int, funct3: int, fd: int, fs1: int, fs2: int, fs3: int):
#     return struct.pack("<I", opcode | fd << 7 | funct3 << 12 | fs1 << 15 | fs2 << 20 | funct2 << 25 | fs3 << 27)
#
#
# def pack_I(opcode: int, funct3: int, rd: int, rs1: int, imm: int):
#     return struct.pack("<I", opcode | rd << 7 | funct3 << 12 | rs1 << 15 | imm << 20)
#
#
# def pack_S(opcode: int, funct3: int, rs1: int, rs2: int, imm: int):
#     return struct.pack("<I", opcode | imm & 0b11111 | (funct3 << 12) | (rs1 << 15) | (rs2 << 20) | ((imm >> 5) << 25))
#
#
# def pack_B(opcode: int, funct3: int, rs1: int, rs2: int, imm: int):
#     return struct.pack("<I", opcode | ((imm >> 11) & 1) | (imm >> 1 & 0b1111) << 1 | (funct3 << 12) | (rs1 << 15) | (
#             rs2 << 20) | ((imm >> 5) << 25) | ((imm >> 12) << 31))
#
#
# def pack_U(opcode: int, rd: int, imm: int):
#     return struct.pack("<I", opcode | (rd << 7) | (imm >> 12) << 12)
#
#
# def pack_J(opcode: int, rd: int, imm: int):
#     return struct.pack("<I", opcode | (rd << 7) | (imm >> 12 & 255) << 12 | (imm >> 11 & 1) << 20 | (
#             imm >> 1 & 1023) << 21 | (imm >> 20) << 31)


class S(Asm):
    def __init__(self, rs1, rs2, imm: int):
        assert isinstance(imm, int) and -2048 <= imm <= 2047
        self.rs1 = rs1
        self.rs2 = rs2
        self.imm = imm

    def __repr__(self) -> str:
        assert self.opcode != ''
        return f"<{self.opcode} {self.rs1}, {self.imm:+}({self.rs2})>"

    def pack(self):
        return pack_S(self.opcode, self.funct3, int(self.rs1), int(self.rs2), self.imm)


class I(Asm):
    def __init__(self, rd, rs1, imm: int):
        assert isinstance(imm, int) and -2048 <= imm <= 2047
        self.rd, self.rs1, self.imm = rd, rs1, imm

    def __repr__(self) -> str:
        assert self.opcode != ''
        return f"<{self.opcode} {self.rd}, {self.rs1}, {self.imm:+}>"


class U(Asm):

    def __init__(self, rd, imm: int):
        self.rd, self.imm = rd, imm

    def __repr__(self) -> str:
        return f"<{self.opcode} {self.rd}, {self.imm}>"


class B(Asm):
    opcode = ''

    def __init__(self, rs1, rs2, imm: int):
        assert isinstance(imm, int) and -2048 <= imm <= 2047
        self.rs1 = rs1
        self.rs2 = rs2
        self.imm = imm

    def __repr__(self) -> str:
        assert self.opcode != ''
        return f"<{self.opcode} {self.rs1}, {self.rs2}, {self.imm:+}>"


class Add(R): opcode = "add"


class Sub(R): opcode = "sub"


class Xor(R): opcode = "xor"


class And(R): opcode = "and"


class Slt(R): opcode = "slt"


class Sltu(R): opcode = "sltu"


class FAdd(R): opcode = "fadd.s"


class FSub(R): opcode = "fsub.s"


class FMul(R): opcode = "fmul.s"


class FDiv(R): opcode = "fdiv.s"


class FSgnjN(R): opcode = "fsgnjn.s"


class FSgnjX(R): opcode = "fsgnjx.s"


class FEq(R): opcode = "feq.s"


class FLt(R): opcode = "flt.s"


class FLe(R): opcode = "fle.s"


# class FClass(R): opcode = "fclass.s"
class FMvXW(R): opcode = "fmv.x.w"; rs2 = Rs2Disabled()


class FMvWX(R): opcode = "fmv.w.x"; rs2 = Rs2Disabled()


class Lui(U): opcode = "lui"


class Auipc(U): opcode = "auipc"


class FLw(I): opcode = "flw"


class Addi(I): opcode = "addi"


class Xori(I): opcode = "xori"


class Andi(I): opcode = "andi"


class Slti(I): opcode = "slti"


class Sltiu(I):
    opcode = "sltiu"


class Beq(B):
    opcode = "beq"


class Bne(B):
    opcode = "bne"


class Blt(B):
    opcode = "blt"


class Bge(B):
    opcode = "bge"


class Bltu(B):
    opcode = "bltu"


class Bgeu(B):
    opcode = "bgeu"


class Jal(Asm):
    opcode = "jal"

    def __init__(self, rd: ABIName, imm: int):
        assert isinstance(rd, ABIName)
        assert isinstance(imm, int) and -2048 <= imm <= 2047
        self.rd = rd
        self.imm = imm

    def __repr__(self):
        return f"<jal {self.rd}, {self.imm:+}>"


class Jalr(I): opcode = "jalr"



class MachineBasicBlock:
    def __init__(self):
        self.predecessors: list[MachineBasicBlock] = []
        self.successors: list[MachineBasicBlock] = []


class Phi(Asm):
    def __init__(self):
        self.incoming: list[tuple[..., MachineBasicBlock]] = []
