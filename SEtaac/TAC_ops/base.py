

# This is the object exported from Gigahorse
class TAC_Statement:
    __name__ = "TAC_Statement"
    __internal_name__ = ""
    def __init__(self, TACblock_ident, ident, opcode, operands=None, defs=None, values=None):
        self.tac_block_id = TACblock_ident
        self.ident = ident
        self.opcode = opcode
        self.operands = operands if operands else list()
        self.defs = defs if defs else list()
        self.values = values if values else dict()
    
    def __str__(self):
        return "TACStatement[blockid:{}|stmtid:{}] | opcode: {} | operands:{} | defs:{} | values:{}".format(self.tac_block_id, 
                                                                                                            self.ident,
                                                                                                            self.opcode, 
                                                                                                            self.operands,
                                                                                                            self.defs,
                                                                                                            self.values)

class Aliased:
    __aliases__ = dict()

    def __getattr__(self, key):
        if key in self.__aliases__:
            aliased_key = self.__aliases__[key]
            return self.__dict[aliased_key]
        else:
            return self.__dict[key]

    def __setattr__(self, key, value):
        if key in self.__aliases__:
            aliased_key = self.__aliases__[key]
            self.__dict[aliased_key] = value
        else:
            self.__dict[key] = value


class TAC_NoOperands(Aliased):
    __internal_name__ = None

    def __init__(self):
        self.res_var = None
        self.res_val = None

    def parse(self, raw_stmt:TAC_Statement):
        self.res_var = raw_stmt.defs[0]
        self.res_val = raw_stmt.values.get(self.res_var, None)

    def __str__(self):
        res = self.res_var if not self.res_val else self.res_var + '({})'.format(self.res_val)
        return "{} = {}".format(res, self.__internal_name__)

class TAC_Unary(Aliased):
    __internal_name__ = None

    def __init__(self):
        self.op1_var = None
        self.res_var = None

        self.op1_val = None
        self.res_val = None

    def parse(self, raw_stmt:TAC_Statement):
        self.op1_var = raw_stmt.operands[0]
        self.res_var = raw_stmt.defs[0]

        self.op1_val = raw_stmt.values.get(self.op1_var, None)
        self.res_val = raw_stmt.values.get(self.res_var, None)

    def __str__(self):
        op1 = self.op1_var if not self.op1_val else self.op1_var + '({})'.format(self.op1_val)
        res = self.res_var if not self.res_val else self.res_var + '({})'.format(self.res_val)
        return "{} = {} {}".format(res, self.__internal_name__, op1)

class TAC_UnaryNoRes(Aliased):
    __internal_name__ = None

    def __init__(self):
        self.op1_var = None
        self.op1_val = None

    def parse(self, raw_stmt:TAC_Statement):
        self.op1_var = raw_stmt.operands[0]
        self.op1_val = raw_stmt.values.get(self.op1_var, None)

    def __str__(self):
        op1 = self.op1_var if not self.op1_val else self.op1_var + '({})'.format(self.op1_val)
        return "{} {}".format(self.__internal_name__, op1)

class TAC_Binary(Aliased):
    __internal_name__ = None

    def __init__(self):
        self.op1_var = None
        self.op2_var = None
        self.res_var = None

        self.op1_val = None
        self.op2_val = None
        self.res_val = None

    def parse(self, raw_stmt:TAC_Statement):
        self.op1_var = raw_stmt.operands[0]
        self.op2_var = raw_stmt.operands[1]
        self.res_var = raw_stmt.defs[0]

        self.op1_val = raw_stmt.values.get(self.op1_var, None)
        self.op2_val = raw_stmt.values.get(self.op2_var, None)
        self.res_val = raw_stmt.values.get(self.res_var, None)

    def __str__(self):
        op1 = self.op1_var if not self.op1_val else self.op1_var + '({})'.format(self.op1_val)
        op2 = self.op2_var if not self.op2_val else self.op2_var + '({})'.format(self.op2_val)
        res = self.res_var if not self.res_val else self.res_var + '({})'.format(self.res_val)
        return "{} = {} {} {}".format(res, op1, self.__internal_name__, op2)


class TAC_BinaryNoRes(Aliased):
    __internal_name__ = None

    def __init__(self):
        self.op1_var = None
        self.op2_var = None
        self.op1_val = None
        self.op2_val = None

    def parse(self, raw_stmt:TAC_Statement):
        self.op1_var = raw_stmt.operands[0]
        self.op2_var = raw_stmt.operands[1]

        self.op1_val = raw_stmt.values.get(self.op1_var, None)
        self.op2_val = raw_stmt.values.get(self.op2_var, None)

    def __str__(self):
        op1 = self.op1_var if not self.op1_val else self.op1_var + '({})'.format(self.op1_val)
        op2 = self.op2_var if not self.op2_val else self.op2_var + '({})'.format(self.op2_val)
        return "{} {} {}".format(op1, self.__internal_name__, op2)

class TAC_Ternary(Aliased):
    __internal_name__ = None

    def __init__(self):
        self.op1_var = None
        self.op2_var = None
        self.op3_var = None
        self.res_var = None

        self.op1_val = None
        self.op2_val = None
        self.op3_val = None
        self.res_val = None

    def parse(self, raw_stmt:TAC_Statement):
        self.op1_var = raw_stmt.operands[0]
        self.op2_var = raw_stmt.operands[1]
        self.op3_var = raw_stmt.operands[2]
        self.res_var = raw_stmt.defs[0]

        self.op1_val = raw_stmt.values.get(self.op1_var, None)
        self.op2_val = raw_stmt.values.get(self.op2_var, None)
        self.op3_val = raw_stmt.values.get(self.op3_var, None)
        self.res_val = raw_stmt.values.get(self.res_var, None)

    def __str__(self):
        op1 = self.op1_var if not self.op1_val else self.op1_var + '({})'.format(self.op1_val)
        op2 = self.op2_var if not self.op2_val else self.op2_var + '({})'.format(self.op2_val)
        op3 = self.op3_var if not self.op3_val else self.op3_var + '({})'.format(self.op3_val)
        res = self.res_var if not self.res_val else self.res_var + '({})'.format(self.res_val)
        return "{} = {} ({} {} {})".format(res, self.__internal_name__, op1, op2, op3)

class TAC_TernaryNoRes(Aliased):
    __internal_name__ = None

    def __init__(self):
        self.op1_var = None
        self.op2_var = None
        self.op3_var = None

        self.op1_val = None
        self.op2_val = None
        self.op3_val = None

    def parse(self, raw_stmt:TAC_Statement):
        self.op1_var = raw_stmt.operands[0]
        self.op2_var = raw_stmt.operands[1]
        self.op3_var = raw_stmt.operands[2]

        self.op1_val = raw_stmt.values.get(self.op1_var, None)
        self.op2_val = raw_stmt.values.get(self.op2_var, None)
        self.op3_val = raw_stmt.values.get(self.op3_var, None)

    def __str__(self):
        op1 = self.op1_var if not self.op1_val else self.op1_var + '({})'.format(self.op1_val)
        op2 = self.op2_var if not self.op2_val else self.op2_var + '({})'.format(self.op2_val)
        op3 = self.op3_var if not self.op3_val else self.op3_var + '({})'.format(self.op3_val)
        return "{} ({} {} {})".format(self.__internal_name__, op1, op2, op3)

class TAC_Quaternary(Aliased):
    __internal_name__ = None

    def __init__(self):
        self.op1_var = None
        self.op2_var = None
        self.op3_var = None
        self.op4_var = None
        self.res_var = None
        

        self.op1_val = None
        self.op2_val = None
        self.op3_val = None
        self.op4_val = None
        self.res_val = None

    def parse(self, raw_stmt:TAC_Statement):
        self.op1_var = raw_stmt.operands[0]
        self.op2_var = raw_stmt.operands[1]
        self.op3_var = raw_stmt.operands[2]
        self.op4_var = raw_stmt.operands[3]
        self.res_var = raw_stmt.defs[0]


        self.op1_val = raw_stmt.values.get(self.op1_var, None)
        self.op2_val = raw_stmt.values.get(self.op2_var, None)
        self.op3_val = raw_stmt.values.get(self.op3_var, None)
        self.op4_val = raw_stmt.values.get(self.op4_var, None)
        self.res_val = raw_stmt.values.get(self.res_var, None)

    def __str__(self):
        op1 = self.op1_var if not self.op1_val else self.op1_var + '({})'.format(self.op1_val)
        op2 = self.op2_var if not self.op2_val else self.op2_var + '({})'.format(self.op2_val)
        op3 = self.op3_var if not self.op3_val else self.op3_var + '({})'.format(self.op3_val)
        op4 = self.op4_var if not self.op4_val else self.op4_var + '({})'.format(self.op4_val)
        res = self.res_var if not self.res_val else self.res_var + '({})'.format(self.res_val)
        return "{} = {} ({} {} {} {})".format(res, self.__internal_name__, op1, op2, op3, op4)

class TAC_QuaternaryNoRes(Aliased):
    __internal_name__ = None

    def __init__(self):
        self.op1_var = None
        self.op2_var = None
        self.op3_var = None
        self.op4_var = None

        self.op1_val = None
        self.op2_val = None
        self.op3_val = None
        self.op4_val = None

    def parse(self, raw_stmt:TAC_Statement):
        self.op1_var = raw_stmt.operands[0]
        self.op2_var = raw_stmt.operands[1]
        self.op3_var = raw_stmt.operands[2]
        self.op4_var = raw_stmt.operands[3]

        self.op1_val = raw_stmt.values.get(self.op1_var, None)
        self.op2_val = raw_stmt.values.get(self.op2_var, None)
        self.op3_val = raw_stmt.values.get(self.op3_var, None)
        self.op4_val = raw_stmt.values.get(self.op4_var, None)

    def __str__(self):
        op1 = self.op1_var if not self.op1_val else self.op1_var + '({})'.format(self.op1_val)
        op2 = self.op2_var if not self.op2_val else self.op2_var + '({})'.format(self.op2_val)
        op3 = self.op3_var if not self.op3_val else self.op3_var + '({})'.format(self.op3_val)
        op4 = self.op4_var if not self.op4_val else self.op4_var + '({})'.format(self.op4_val)
        return "{} = {} ({} {} {} {})".format(self.__internal_name__, op1, op2, op3, op4)

class TAC_Senary(Aliased):
    __internal_name__ = None

    def __init__(self):
        self.op1_var = None
        self.op2_var = None
        self.op3_var = None
        self.op4_var = None
        self.op5_var = None
        self.op6_var = None
        self.res_var = None

        self.op1_val = None
        self.op2_val = None
        self.op3_val = None
        self.op4_val = None
        self.op5_val = None
        self.op6_val = None
        self.res_val = None

    def parse(self, raw_stmt:TAC_Statement):
        self.op1_var = raw_stmt.operands[0]
        self.op2_var = raw_stmt.operands[1]
        self.op3_var = raw_stmt.operands[2]
        self.op4_var = raw_stmt.operands[3]
        self.op5_var = raw_stmt.operands[4]
        self.op6_var = raw_stmt.operands[5]
        self.res_var = raw_stmt.defs[0]

        self.op1_val = raw_stmt.values.get(self.op1_var, None)
        self.op2_val = raw_stmt.values.get(self.op2_var, None)
        self.op3_val = raw_stmt.values.get(self.op3_var, None)
        self.op4_val = raw_stmt.values.get(self.op4_var, None)
        self.op5_val = raw_stmt.values.get(self.op5_var, None)
        self.op6_val = raw_stmt.values.get(self.op6_var, None)
        self.res_val = raw_stmt.values.get(self.res_var, None)

    def __str__(self):
        op1 = self.op1_var if not self.op1_val else self.op1_var + '({})'.format(self.op1_val)
        op2 = self.op2_var if not self.op2_val else self.op2_var + '({})'.format(self.op2_val)
        op3 = self.op3_var if not self.op3_val else self.op3_var + '({})'.format(self.op3_val)
        op4 = self.op4_var if not self.op4_val else self.op4_var + '({})'.format(self.op4_val)
        op5 = self.op5_var if not self.op5_val else self.op5_var + '({})'.format(self.op5_val)
        op6 = self.op6_var if not self.op6_val else self.op6_var + '({})'.format(self.op6_val)
        res = self.res_var if not self.res_val else self.res_var + '({})'.format(self.res_val)
        return "{} = {} {} {} {} {} {} {}".format(res, self.__internal_name__, op1, op2, op3, op4, op5, op6)

class TAC_Septenary(Aliased):
    __internal_name__ = None

    def __init__(self):
        self.op1_var = None
        self.op2_var = None
        self.op3_var = None
        self.op4_var = None
        self.op5_var = None
        self.op6_var = None
        self.op7_var = None
        self.res_var = None

        self.op1_val = None
        self.op2_val = None
        self.op3_val = None
        self.op4_val = None
        self.op5_val = None
        self.op6_val = None
        self.op7_val = None
        self.res_val = None

    def parse(self, raw_stmt:TAC_Statement):
        self.op1_var = raw_stmt.operands[0]
        self.op2_var = raw_stmt.operands[1]
        self.op3_var = raw_stmt.operands[2]
        self.op4_var = raw_stmt.operands[3]
        self.op5_var = raw_stmt.operands[4]
        self.op6_var = raw_stmt.operands[5]
        self.op7_var = raw_stmt.operands[6]
        self.res_var = raw_stmt.defs[0]

        self.op1_val = raw_stmt.values.get(self.op1_var, None)
        self.op2_val = raw_stmt.values.get(self.op2_var, None)
        self.op3_val = raw_stmt.values.get(self.op3_var, None)
        self.op4_val = raw_stmt.values.get(self.op4_var, None)
        self.op5_val = raw_stmt.values.get(self.op5_var, None)
        self.op6_val = raw_stmt.values.get(self.op6_var, None)
        self.op7_val = raw_stmt.values.get(self.op7_var, None)
        self.res_val = raw_stmt.values.get(self.res_var, None)

    def __str__(self):
        op1 = self.op1_var if not self.op1_val else self.op1_var + '({})'.format(self.op1_val)
        op2 = self.op2_var if not self.op2_val else self.op2_var + '({})'.format(self.op2_val)
        op3 = self.op3_var if not self.op3_val else self.op3_var + '({})'.format(self.op3_val)
        op4 = self.op4_var if not self.op4_val else self.op4_var + '({})'.format(self.op4_val)
        op5 = self.op5_var if not self.op5_val else self.op5_var + '({})'.format(self.op5_val)
        op6 = self.op6_var if not self.op6_val else self.op6_var + '({})'.format(self.op6_val)
        op7 = self.op7_var if not self.op7_val else self.op7_var + '({})'.format(self.op7_val)
        res = self.res_var if not self.res_val else self.res_var + '({})'.format(self.res_val)
        return "{} = {} {} {} {} {} {} {}".format(res, self.__internal_name__, op1, op2, op3, op4, op5, op6, op7)