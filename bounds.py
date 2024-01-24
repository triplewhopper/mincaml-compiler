import linecache


class Bounds:
    __slots__ = '_filepath', '_lineno', '_colno', '_end_lineno', '_end_colno'
    srcs: list[str] = []

    def __init__(self, filepath: str, lineno: int, colno: int, end_lineno: int, end_colno: int):
        assert isinstance(filepath, str)
        assert isinstance(lineno, int) and isinstance(colno, int)
        assert isinstance(end_lineno, int) and isinstance(end_colno, int)
        assert 1 <= lineno and 1 <= colno and 1 <= end_lineno and 1 <= end_colno
        assert lineno == end_lineno and colno <= end_colno or lineno < end_lineno
        self._filepath = filepath
        self._lineno = lineno
        self._colno = colno
        self._end_lineno = end_lineno
        self._end_colno = end_colno

    @property
    def filepath(self) -> str:
        return self._filepath

    @property
    def lineno(self) -> int:
        return self._lineno

    @property
    def colno(self) -> int:
        return self._colno

    @property
    def end_lineno(self) -> int:
        return self._end_lineno

    @property
    def end_colno(self) -> int:
        return self._end_colno

    def replace_with(self, /, *, lineno: int | None = None, colno: int | None = None, end_lineno: int | None = None,
                     end_colno: int | None = None) -> 'Bounds':
        return Bounds(self._filepath,
                      lineno or self._lineno, colno or self._colno,
                      end_lineno or self._end_lineno, end_colno or self._end_colno)

    def isdisjoint(self, other: 'Bounds') -> bool:
        assert self._filepath == other._filepath
        if (self._end_lineno, self._end_colno) <= (other._lineno, other._colno):
            return True
        if (other._end_lineno, other._colno) < (self._lineno, self._colno):
            return True
        return False

    def __eq__(self, other: object):
        if isinstance(other, Bounds):
            return self._filepath == other._filepath and \
                self._lineno == other._lineno and \
                self._colno == other._colno and \
                self._end_lineno == other._end_lineno and \
                self._end_colno == other._end_colno
        return NotImplemented

    def __hash__(self):
        return hash((Bounds, self._filepath, self._lineno, self._colno, self._end_lineno, self._end_colno))

    def __ior__(self, other: 'Bounds'):
        return self.union(other, in_place=True)

    def __or__(self, other: 'Bounds'):
        return self.union(other)

    def __lt__(self, other: 'Bounds') -> bool:
        return (Bounds.srcs.index(self._filepath), self._end_lineno, self._end_colno) <= \
            (Bounds.srcs.index(other._filepath), other._lineno, other._colno)

    def issubset(self, other: 'Bounds') -> bool:
        assert isinstance(other, Bounds)
        if self._filepath == other._filepath:
            return (self._lineno, self._colno) >= (other._lineno, other._colno) and \
                (self._end_lineno, self._end_colno) <= (other._end_lineno, other._end_colno)
        return False

    def union(self, other: 'Bounds', /, in_place: bool = False) -> 'Bounds':
        assert self._filepath == other._filepath
        lineno, colno = min((self._lineno, self._colno), (other._lineno, other._colno))
        end_lineno, end_colno = max((self._end_lineno, self._end_colno), (other._end_lineno, other._end_colno))
        if in_place:
            self._lineno = lineno
            self._colno = colno
            self._end_lineno = end_lineno
            self._end_colno = end_colno
            return self
        return Bounds(self._filepath, lineno, colno, end_lineno, end_colno)

    def __repr__(self):
        if self._lineno == self._end_lineno:
            if self._colno + 1 == self._end_colno:
                return f"{self._filepath!r}:{self._lineno}:{self._colno - 1}"
            return f"{self._filepath!r}:{self._lineno}:{self._colno}-{self._end_colno - 1}"
        return f"{self._filepath!r}:{self._lineno}:{self._colno}-{self._end_lineno}:{self._end_colno - 1}"

    def dump_with(self, msg: str) -> str:
        lines = [linecache.getline(self._filepath, lineno) for lineno in range(self._lineno, self._end_lineno + 1)]
        if len(lines) == 1:
            line = lines[0].rstrip('\n')
            caret = ' ' * (self._colno - 1) + '^' * (self._end_colno - self._colno)
            return f'File {self._filepath!r}, line {self._lineno}:\n' \
                   f'{self._lineno:<4}|  {line}\n' \
                   f'       {caret}\n' \
                   f'{msg}\n'
        else:
            caret = [' ' * (self._colno - 1) + '^' * (len(lines[0]) - self._colno),
                     '^' * (self._end_colno - 1)]
            return f'File {self._filepath!r}, lines {self._lineno}-{self._end_lineno}:\n' \
                   f'{self._lineno:<4}|  {lines[0]}' \
                   f'       {caret[0]}\n' \
                   f'...\n' \
                   f'{self._end_lineno:<4}|  {lines[-1]}' \
                   f'       {caret[1]}\n' \
                   f'{msg}\n'


class HasBounds:
    def __init__(self, bounds: Bounds):
        assert isinstance(bounds, Bounds)
        self._bounds = bounds

    @property
    def bounds(self) -> Bounds:
        return self._bounds


def merge_bounds(x: Bounds, *args: Bounds) -> Bounds:
    i = iter(args)
    try:
        x = x.union(next(i))
    except StopIteration:
        return x
    while True:
        try:
            y = next(i)
            x |= y
        except StopIteration:
            return x
