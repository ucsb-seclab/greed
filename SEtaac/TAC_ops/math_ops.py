

__all__ = ['TAC_Add', 'TAC_Sub', 'TAC_Mul', 'TAC_Div']

class TAC_Add:
    __internal_name__ = "ADD"
    def __init__(self, op1, op2, res):
        self.op1 = op1
        self.op2 = op2
        self.res = res

    def parse(self, raw_stmt):
        pass # todo 

    def __str__(self):
        return "{} = {} + {}".format(self.res, self.op1, self.op2)

class TAC_Sub:
    __internal_name__ = "SUB"
    def __init__(self, op1, op2, res):
        self.op1 = op1
        self.op2 = op2
        self.res = res

    def parse(self, raw_stmt):
        pass # todo 

    def __str__(self):
        return "{} = {} - {}".format(self.res, self.op1, self.op2)

class TAC_Mul:
    __internal_name__ = "MUL"
    def __init__(self, op1, op2, res):
        self.op1 = op1
        self.op2 = op2
        self.res = res

    def parse(self, raw_stmt):
        pass # todo 

    def __str__(self):
        return "{} = {} * {}".format(self.res, self.op1, self.op2)

class TAC_Div:
    __internal_name__ = "DIV"
    def __init__(self, op1, op2, res):
        self.op1 = op1
        self.op2 = op2
        self.res = res

    def parse(self, raw_stmt):
        pass # todo 

    def __str__(self):
        return "{} = {} \ {}".format(self.res, self.op1, self.op2)