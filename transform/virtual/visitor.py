from .virtual import Function, BasicBlock


class FunctionVisitor:

    def visit(self, func: Function):
        func.accept(self)

    def visit_block(self, block: BasicBlock):
        ...
