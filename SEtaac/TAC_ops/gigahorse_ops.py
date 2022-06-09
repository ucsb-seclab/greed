
'''
These are operators specific of the TAC IR
'''

__all__ = ['TAC_Throw', 'TAC_Callprivate', 'TAC_Returnprivate', 'TAC_Phi', 'TAC_Const']

class TAC_Throw:
    __internal_name__ = "THROW"
    def __init__(self, op1, op2, res):
        pass
    def parse(self, raw_stmt):
        pass # todo 
    def __str__(self):
        return "THROW"

class TAC_Callprivate:
    __internal_name__ = "CALLPRIVATE"
    def __init__(self, op1, op2, res):
        pass
    def parse(self, raw_stmt):
        pass # todo 
    def __str__(self):
        return "CALLPRIVATE"

class TAC_Returnprivate:
    __internal_name__ = "RETURNPRIVATE"
    def __init__(self, op1, op2, res):
        pass
    def parse(self, raw_stmt):
        pass # todo 
    def __str__(self):
        return "RETURNPRIVATE"

class TAC_Phi:
    __internal_name__ = "PHI"
    def __init__(self, op1, op2, res):
        pass
    def parse(self, raw_stmt):
        pass # todo 
    def __str__(self):
        return "PHI"

class TAC_Const:
    __internal_name__ = "CONST"
    def __init__(self):
        self.var = None
        self.val = None
    
    def parse(self, raw_stmt):
        self.var = raw_stmt.defs[0]
        self.val = raw_stmt.values[self.var]

    def __str__(self):
        return "CONST"