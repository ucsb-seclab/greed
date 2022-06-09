
from ops import *

class TAC_Add:
    _name = "ADD"
    def __init__(self, op1, op2, res):
        self.op1 = op1
        self.op2 = op2
        self.res = res

    def parse(self, TAC_Statement: raw_stmt):
        pass # todo 

    def __str__(self):
        return "{} = {} + {}".format(self.res, self.op1, self.op2)

class TAC_Sub:
    _name = "SUB"
    def __init__(self, op1, op2, res):
        self.op1 = op1
        self.op2 = op2
        self.res = res

    def parse(self, TAC_Statement: raw_stmt):
        pass # todo 

    def __str__(self):
        return "{} = {} - {}".format(self.res, self.op1, self.op2)

class TAC_Mul:
    _name = "MUL"
    def __init__(self, op1, op2, res):
        self.op1 = op1
        self.op2 = op2
        self.res = res

    def parse(self, TAC_Statement: raw_stmt):
        pass # todo 

    def __str__(self):
        return "{} = {} * {}".format(self.res, self.op1, self.op2)

class TAC_Div:
    _name = "DIV"
    def __init__(self, op1, op2, res):
        self.op1 = op1
        self.op2 = op2
        self.res = res

    def parse(self, TAC_Statement: raw_stmt):
        pass # todo 

    def __str__(self):
        return "{} = {} \ {}".format(self.res, self.op1, self.op2)