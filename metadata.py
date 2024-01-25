from bounds import Bounds
from withbounds import WithBounds


class Metadata:
    ...


class DIScope(Metadata):
    _counter = 0

    def __init__(self, parent: 'DIScope | None' = None, bounds: Bounds | None = None):
        super().__init__()
        self.parent = parent
        self._id = DIScope._counter
        self._bounds = bounds
        DIScope._counter += 1

    @property
    def root(self) -> 'DIScope':
        g = self
        while g.parent is not None:
            g = g.parent
            if g is self:
                raise ValueError("cyclic scope")
        return g

    def __str__(self):
        return f'!{self._id}'

    def __repr__(self):
        return f'!DIScope({self._id}, parent: {self.parent}, bounds: {self._bounds})'


class DILocation(Metadata):
    def __init__(self, scope: DIScope, bounds: Bounds):
        super().__init__()
        self._scope = scope
        self._bounds = bounds

    @property
    def lineno(self):
        return self._bounds.lineno

    @property
    def colno(self):
        return self._bounds.colno
    
    def __or__(self, other: 'DILocation | WithBounds[str]'):
        if isinstance(other, DILocation):
            assert self._scope is other._scope
            return DILocation(self._scope, self._bounds | other._bounds)
        return DILocation(self._scope, self._bounds | other.bounds)
    
    def get_bounds(self):
        return self._bounds

    def __repr__(self):
        return f'!DILocation(line: {self.lineno}, column: {self.colno}, scope: {self._scope})'
    
class DIIntrinsics(Metadata):
    def __init__(self, name: str):
        super().__init__()
        self.name = name

    def __repr__(self):
        return f'!DIIntrinsics({self.name!r})'


class DIVariable(Metadata):
    def __init__(self, name: str, loc: DILocation, scope: DIScope):
        self.name = name
        self.loc = loc
        self.scope = scope

    @staticmethod
    def from_wbs(scope: DIScope, x: WithBounds[str]):
        return DIVariable(x.val, DILocation(scope, x.bounds), scope)

    def __repr__(self):
        return f'!DIVariable({self.name!r}, {self.loc!r}, {self.scope!r})'


class DILocalVariable(DIVariable):
    @staticmethod
    def from_wbs(scope: DIScope, x: WithBounds[str]):
        return DILocalVariable(x.val, DILocation(scope, x.bounds), scope)


class DIGlobalVariable(DIVariable):
    @staticmethod
    def from_wbs(scope: DIScope, x: WithBounds[str]):
        return DIGlobalVariable(x.val, DILocation(scope, x.bounds), scope)

class DIExpression(Metadata):
    def __init__(self, *elems: Metadata):
        self.elems = elems