
from . import *

class TAC_Mstore:
    _name = "MSTORE"
    def __init__(self, val, dest):
        self.val = val
        self.dest = dest

    def parse(self, TAC_Statement: raw_stmt):
        pass # todo 

    def __str__(self):
        return "MSTORE {} {}".format(self.val, self.dest)