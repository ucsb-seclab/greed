
__all__ = ['TAC_Mstore']

class TAC_Mstore:
    __internal_name__ = "MSTORE"
    def __init__(self, val, dest):
        self.val = val
        self.dest = dest

    def parse(self, raw_stmt):
        pass # todo 

    def __str__(self):
        return "MSTORE {} {}".format(self.val, self.dest)