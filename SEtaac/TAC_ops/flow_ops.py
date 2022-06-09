
from ops import *

class TAC_Jump:
    _name = "JUMP"
    def __init__(self, destination):
        self.destination = destination

    def parse(self, TAC_Statement: raw_stmt):
        pass # todo 

    def __str__(self):
        return "JUMP {}".format(self.destination)

class TAC_Jumpi:
    _name = "JUMPI"
    def __init__(self, condition, destination):
        self.condition = condition
        self.destination = destination

    def parse(self, TAC_Statement: raw_stmt):
        pass # todo 

    def __str__(self):
        return "JUMPI {} {}".format(self.condition, self.destination)