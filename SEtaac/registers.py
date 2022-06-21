from collections import defaultdict

from SEtaac.utils import concrete


class SymbolicRegisters(defaultdict):
    def __init__(self):
        super(SymbolicRegisters, self).__init__(None)
        self.access_order = list()

    def __setitem__(self, key, value):
        # keep track of accesses
        if key in self.access_order:
            self.access_order.remove(key)
        self.access_order.append(key)

        if concrete(value):
            value %= 2 ** 256
        super(SymbolicRegisters, self).__setitem__(key, value)

    def last_accessed(self, keys):
        return [k for k in self.access_order if k in keys][-1]

    def copy(self):
        cls = self.__class__
        new = cls.__new__(cls)
        new.update(self)
        new.access_order = list(self.access_order)
        return new
