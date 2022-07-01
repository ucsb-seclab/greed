from SEtaac.utils.solver.shortcuts import *


class SymbolicStorage(object):
    def __init__(self, xid: int, partial_init=False):
        if partial_init:
            return
        self.base = Array(f'STORAGE_{xid}', BVSort(256), BVSort(256))
        self.storage = self.base
        self.accesses = list()

    def __getitem__(self, index):
        self.accesses.append(('read', index))
        return Array_Select(self.storage, index)

    def __setitem__(self, index, v):
        self.accesses.append(('write', index))
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
        if old_xid != new_xid:
            raise Exception("storage copy with different xid is not implemented. Please have a look")
        new_storage = SymbolicStorage(new_xid, partial_init=True)
        new_storage.base = self.base
        new_storage.storage = self.storage
        new_storage.accesses = self.accesses
        return new_storage
