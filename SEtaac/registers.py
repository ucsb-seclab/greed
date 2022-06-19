from collections import defaultdict

from SEtaac.utils import concrete


class SymbolicRegisters(defaultdict):
    def __setitem__(self, key, value):
        if concrete(value):
            value %= 2 ** 256
        super(SymbolicRegisters, self).__setitem__(key, value)
