from SEtaac.utils import concrete, translate_xid

from SEtaac.utils.solver.shortcuts import *


class SymbolicStorage(object):
    def __init__(self, xid: int):
        self.base = Array(f'STORAGE_{xid}', BVSort(256), BVSort(256))
        self.storage = self.base
        self.accesses = list()

    def __getitem__(self, index):
        self.accesses.append(('read', index if concrete(index) else index))
        return Array_Select(self.storage, index)

    def __setitem__(self, index, v):
        self.accesses.append(('write', index if concrete(index) else index))
        self.storage = Array_Store(self.storage, index, v)

    @property
    def reads(self):
        return [a for t, a in self.accesses if t == 'read']

    @property
    def writes(self):
        return [a for t, a in self.accesses if t == 'write']

    @property
    def all(self):
        return [a for t, a in self.accesses]

    def copy(self, old_xid: int, new_xid: int):
        new_storage = SymbolicStorage(new_xid)
        new_storage.base = translate_xid(self.base, old_xid, new_xid)
        new_storage.storage = translate_xid(self.storage, old_xid, new_xid)
        new_storage.accesses = [(t, a if concrete(a) else translate_xid(a, old_xid, new_xid)) for t, a in self.accesses]
        return new_storage
