class SymbolicRegisters(dict):
    def __init__(self):
        super(SymbolicRegisters, self).__init__()

    def __setitem__(self, key, value):
        super(SymbolicRegisters, self).__setitem__(key, value)

    def copy(self):
        cls = self.__class__
        new = cls.__new__(cls)
        new.update(self)
        return new
