import knormal as K

class Alpha(K.KNormalVisitor):
    def __init__(self):
        self.env = {}
        self.cnt = 0

    def visit_var(self, e: K.Var) -> K.Var:
        ...