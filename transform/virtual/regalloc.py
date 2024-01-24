from .virtual import *

class CodeGen:
    def __init__(self, func: Function):
        self.func = func
        self.registers = {}
        self.stack = []
        self.instructions = []

    def gen(self):
        self.visit(self.func)

    def visit(self, func: Function):
        for block in func.blocks:
            self.visit_block(block)

    def visit_block(self, block: BasicBlock):
        for inst in block.instructions:
            self.visit_inst(inst)

    def visit_inst(self, inst: Instr):
        if isinstance(inst, Load):
            if isinstance(inst.rs, GetElementPtr):
                self.instructions.append({'op':'load', 'rd': inst.rd, 'rs': inst.rs})
            self.instructions.append(['load', inst.rd, inst.rs])
        elif isinstance(inst, Store):
            self.visit_store(inst)
        elif isinstance(inst, Arith2):
            self.visit_binary(inst)
        elif isinstance(inst, Unary):
            self.visit_unary(inst)
        elif isinstance(inst, Call):
            self.visit_call(inst)
        elif isinstance(inst, Jump):
            self.visit_jump(inst)
        elif isinstance(inst, Branch):
            self.visit_branch(inst)
        elif isinstance(inst, Return):
            self.visit_return(inst)
        else:
            raise NotImplementedError

    def visit_load(self, inst: Load):
        self.registers[inst.dest] = inst.src

    def visit_store(self, inst: Store):
        self.instructions.append(f"store {self.registers[inst.src]} {inst.dest}")

    def visit_binary(self, inst: Arith2):
        self.registers[inst.dest] = f"{inst.op} {self.registers[inst.left]} {self.registers[inst.right]}"

    def visit_unary(self, inst: Arith1):
        self.registers[inst.dest] = f"{inst.op} {self.registers[inst.src]}"

    def visit_call(self, inst: Call):
        self.instructions.append(f"call {inst.func} {inst.dest} {inst.args}")

    def visit_jump(self, inst: Jump):
        self.instructions.append(f"jump {inst.dest}")

    def visit_branch(self, inst: Branch):
        self.instructions.append(f"branch {self.registers[inst.cond]} {inst.true} {inst.false}")

    def visit_return(self, inst: Return):
        self.instructions.append(f"return {self.registers[inst.src]}")