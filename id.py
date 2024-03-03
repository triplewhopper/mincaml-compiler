# from abc import ABC, abstractmethod
from metadata import DIVariable, DIIntrinsics


# from bounds import Bounds

class Id:
    __slots__ = '_id', '_descr'
    _counter = 0
    di_vars: dict['Id', DIVariable | DIIntrinsics] = {}

    def __init__(self, descr: str = ''):
        self._id = Id._counter
        self._descr = descr
        Id._counter += 1

    def __eq__(self, __value: object):
        if isinstance(__value, Id):
            return self._id == __value._id
        return NotImplemented

    def __hash__(self):
        return hash(self._id)

    def __str__(self):
        try:
            return self.di_vars[self].name
        except KeyError:
            if self._descr:
                return f".{self._id}_L{self._descr}_J"
            return f".{self._id}"

    def __repr__(self):
        return f"<id {self._id}>"

    def dump_as_label(self):
        s = str(self)
        if '%' in s:
            return f'"{s}"'
        return s
    
    def add_to_intrinsics(self, name: str):
        Id.di_vars[self] = DIIntrinsics(name)
    
    def is_intrinsic(self, name: str | None = None):
        if name is None:
            return isinstance(Id.di_vars.get(self), DIIntrinsics)
        return isinstance(Id.di_vars.get(self), DIIntrinsics) and Id.di_vars[self].name == name

    def is_main(self):
        return self._descr == 'main'