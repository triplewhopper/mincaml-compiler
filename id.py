# from abc import ABC, abstractmethod
from metadata import DIVariable


class Id:
    _counter = 0

    def __init__(self, metadata: DIVariable | None = None):
        self.metadata = metadata
        self._id = Id._counter
        Id._counter += 1

    def __eq__(self, __value: object):
        if isinstance(__value, Id):
            return self._id == __value._id
        return NotImplemented

    def __hash__(self):
        return hash((Id, self._id))

    @property
    def is_tmp(self):
        return self.metadata is None

# class Id(ABC):
#     __slots__ = '_ir_prefix'
#     _deduplication: dict[str, dict[WBs[str], int]] = {}

#     def __init__(self):
#         self._ir_prefix = '%'

#     def set_ir_prefix_as_global(self):
#         self._ir_prefix = '@'

#     @property
#     @abstractmethod
#     def bounds(self) -> Bounds | None:
#         ...

#     @abstractmethod
#     def dump(self, prefix: bool = True) -> str:
#         ...

#     @abstractmethod
#     def suffix(self, suffix: str) -> 'SuffixId':
#         ...


# def _tmp_id_factory():
#     i = 0
#     while True:
#         yield TmpId(i)
#         i += 1


# tmp_id_factory = _tmp_id_factory()


# class TmpId(Id):
#     __slots__ = 'idx', '_bounds'

#     def __init__(self, idx: int):
#         super(TmpId, self).__init__()
#         assert isinstance(idx, int) and idx >= 0
#         self.idx = idx
#         self._bounds: Bounds | None = None

#     @property
#     def bounds(self) -> Bounds | None:
#         return self._bounds

#     @bounds.setter
#     def bounds(self, bounds: Bounds):
#         assert isinstance(bounds, Bounds)
#         assert self._bounds is None
#         self._bounds = bounds

#     def __str__(self):
#         return f"__{self.idx}"

#     def dump(self, prefix: bool = True) -> str:
#         if prefix: return f"{self._ir_prefix}{self.idx}"
#         return f"{self.idx}"

#     def __repr__(self):
#         return f"TmpId({self.idx})"

#     def __hash__(self):
#         return hash((TmpId, self.idx))

#     def __eq__(self, other: object):
#         match other:
#             case TmpId(idx=idx):
#                 return self.idx == idx
#             case _:
#                 return False

#     def suffix(self, suffix: str) -> 'SuffixId':
#         return SuffixId(self, suffix)


# class LocalId(Id):
#     __slots__ = 'val', 'defn'

#     def __init__(self, val: WBs[str], defn: WBs[str]):
#         assert isinstance(val, WBs) and isinstance(val.val, str)
#         assert isinstance(defn, WBs) and isinstance(defn.val, str)
#         assert val.val == defn.val
#         super(LocalId, self).__init__()
#         self.val = val
#         self.defn = defn
#         if self.val.val not in Id._deduplication:
#             Id._deduplication[self.val.val] = {}
#         sz = len(Id._deduplication[self.val.val])
#         Id._deduplication[self.val.val].setdefault(self.defn, sz)

#     @staticmethod
#     def create_definition(defn: WBs[str]):
#         return LocalId(defn, defn)

#     @classmethod
#     def clear_deduplication(cls):
#         cls._deduplication.clear()

#     @property
#     def is_definition(self) -> bool:
#         return self.val.bounds == self.defn.bounds

#     def __eq__(self, other: object):
#         if isinstance(other, LocalId):
#             return self.val.val == other.val.val and self.defn.bounds == other.defn.bounds
#         return False

#     def __hash__(self):
#         return hash((LocalId, self.defn))

#     def new_usage(self, bounds: Bounds) -> 'LocalId':
#         assert bounds != self.defn.bounds
#         val = WBs(self.val.val, bounds)
#         return LocalId(val, self.defn)

#     @property
#     def bounds(self) -> Bounds:
#         return self.val.bounds

#     def dump(self, prefix: bool = True) -> str:
#         prefix2 = self._ir_prefix if prefix else ''
#         if (_s := len(Id._deduplication[self.val.val])) == 1:
#             return f'{prefix2}{self.val.val}'
#         else:
#             i = Id._deduplication[self.val.val][self.defn]
#             return f"{prefix2}{self.val.val}.{i + 1}"
#             # if i == 0:
#             #     return f"{prefix}{self.val.val}.1st.in.{s}"
#             # elif i == 1:
#             #     return f"{prefix}{self.val.val}.2nd.in.{s}"
#             # elif i == 2:
#             #     return f"{prefix}{self.val.val}.3rd.in.{s}"
#             # return f"{prefix}{self.val.val}.{i + 1}th.in.{s}"

#     def __str__(self):
#         if (s := len(Id._deduplication[self.val.val])) == 1:
#             return self.val.val
#         else:
#             i = Id._deduplication[self.val.val][self.defn]
#             return f"{self.val.val} (* no.{i + 1}/{s} *)"

#     def __repr__(self):
#         if self.is_definition:
#             return f"<{self.val.val!r}@{self.val.bounds}>"
#         return f"<{self.val.val!r}@{self.val.bounds}, defined at {self.defn.bounds}>"

#     def suffix(self, suffix: str) -> 'SuffixId':
#         return SuffixId(self, suffix)

# class GlobalId(Id):
#     __slots__ = '_val', '_defn'

#     def __init__(self, val: WBs[str], defn: WBs[str] | None = None):
#         super(GlobalId, self).__init__()
#         assert isinstance(val, WBs) and isinstance(val.val, str)
#         assert defn is None or isinstance(defn, WBs) and isinstance(defn.val, str) and val.val == defn.val
#         self._val = val
#         self._defn = defn
#         self.set_ir_prefix_as_global()

#     @property
#     def val(self) -> WBs[str]:
#         return self._val

#     @property
#     def is_external(self) -> bool:
#         return self._defn is None

#     def __repr__(self):
#         if self._defn is None:
#             return f"<external {self._val.val!r}@{self._val.bounds}>"
#         return f"<global {self._val.val!r}@{self._val.bounds}, defined at {self._defn.bounds}>"

#     def new_usage(self, bounds: Bounds) -> 'GlobalId':
#         assert bounds != self.val.bounds
#         return GlobalId(WBs(self.val.val, bounds), self._defn)

#     def dump(self, prefix: bool = True) -> str:
#         if prefix: return f"{self._ir_prefix}{self.val.val}"
#         return self.val.val

#     def __str__(self):
#         if self.is_external:
#             return self.val.val + ' (* external *)'
#         return self.val.val

#     def __eq__(self, other: object):
#         if isinstance(other, GlobalId):
#             match self._defn, other._defn:
#                 case None, None:
#                     return self._val.val == other._val.val
#                 case [_, None] | [None, _]:
#                     return False
#                 case defn, defn2:
#                     return self._val.val == other._val.val and defn.bounds == defn2.bounds
#         return False

#     def __hash__(self):
#         if self._defn is not None:
#             return hash((GlobalId, self._defn))
#         return hash((GlobalId, self._val))

#     @property
#     def bounds(self) -> Bounds:
#         return self.val.bounds

#     def suffix(self, suffix: str) -> 'SuffixId':
#         return SuffixId(self, suffix)


# class SuffixId(Id):
#     __slots__ = 'parent', '_suffix', '__dump', 'serial_number'
#     _scope = dict[str, int]()

#     def __init__(self, parent: 'LocalId | GlobalId | TmpId | SuffixId', suffix: str):
#         assert isinstance(parent, Id)
#         assert isinstance(suffix, str)
#         assert suffix != ''
#         super(SuffixId, self).__init__()
#         self.parent = parent
#         self._suffix = suffix
#         self.__dump = f"{self.parent.dump(False)}.{self._suffix}"
#         self.serial_number = self._scope.setdefault(self.__dump, 0)
#         self._scope[self.__dump] += 1

#     def suffix(self, suffix: str) -> 'SuffixId':
#         return SuffixId(self, suffix)

#     @property
#     def bounds(self) -> Bounds | None:
#         return None

#     def dump(self, prefix: bool = True) -> str:
#         prefix2 = self._ir_prefix if prefix else ''
#         return prefix2 + (self.__dump + f".{self.serial_number}" if self.serial_number > 0 else self.__dump)

#     def __str__(self):
#         return f"{self.parent}.{self._suffix}"

#     def __repr__(self):
#         return f"{self.parent!r}.{self._suffix}"

#     def __eq__(self, other: object) -> bool:
#         if isinstance(other, SuffixId):
#             return self._suffix == other._suffix and self.serial_number == other.serial_number and self.parent == other.parent
#         return False

#     def __hash__(self):
#         return hash((SuffixId, self.parent, self._suffix, self.serial_number))
