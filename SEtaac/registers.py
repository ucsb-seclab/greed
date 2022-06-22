from SEtaac.utils import concrete


class SymbolicRegisters(dict):
    def __init__(self):
        super(SymbolicRegisters, self).__init__()

    def __setitem__(self, key, value):
        if concrete(value):
            value %= 2 ** 256
        super(SymbolicRegisters, self).__setitem__(key, value)
