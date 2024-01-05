import knormal as K
_not = K.Function("not", ["x"], K.If(K.Binary("==", "x", 0), 1, 0))
class RegAlloc(K.KNormalVisitor):
    def __init__(self):
        self.reg = {}
        self.stack = []
        self.offset = 0