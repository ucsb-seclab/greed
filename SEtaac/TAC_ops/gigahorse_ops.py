
'''
These are operators specific of the TAC IR
'''

from . import *

class TAC_Throw:
    _name = "THROW"
    def __init__(self, op1, op2, res):
        pass
    def parse(self, TAC_Statement: raw_stmt):
        pass # todo 
    def __str__(self):
        return "THROW"

class TAC_Callprivate:
    _name = "CALLPRIVATE"
    def __init__(self, op1, op2, res):
        pass
    def parse(self, TAC_Statement: raw_stmt):
        pass # todo 
    def __str__(self):
        return "CALLPRIVATE"

class TAC_Returnprivate:
    _name = "RETURNPRIVATE"
    def __init__(self, op1, op2, res):
        pass
    def parse(self, TAC_Statement: raw_stmt):
        pass # todo 
    def __str__(self):
        return "RETURNPRIVATE"

class TAC_Phi:
    _name = "PHI"
    def __init__(self, op1, op2, res):
        pass
    def parse(self, TAC_Statement: raw_stmt):
        pass # todo 
    def __str__(self):
        return "PHI"

class TAC_Const:
    _name = "CONST"
    def __init__(self, op1, op2, res):
        pass
    def parse(self, TAC_Statement: raw_stmt):
        pass # todo 
    def __str__(self):
        return "CONST"