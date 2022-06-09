
__all__ = ['TAC_Mstore']

class TAC_Mstore:
    __internal_name__ = "MSTORE"

    def __init__(self):
        self.offset_var = None
        self.data_var = None
        self.offset_val = None
        self.data_val = None
        
    def parse(self, raw_stmt):
        self.offset_var = raw_stmt.operands[0]
        self.data_var = raw_stmt.operands[1]
        self.offset_val = raw_stmt.values.get(self.offset_var, None)
        self.data_val = raw_stmt.values.get(self.data_var, None) 

    def __str__(self):
        op1 = self.offset_var if not self.offset_val else self.offset_var + '({})'.format(self.offset_val)
        op2 = self.data_var if not self.data_val else self.data_var + '({})'.format(self.data_val)
        return "MSTORE {} {}".format(op1,op2)