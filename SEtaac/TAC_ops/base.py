
from SEtaac.state import SymbolicEVMState

# This is the object exported from Gigahorse
class TAC_Statement:
    __name__ = "TAC_Statement"
    __internal_name__ = ""
    def __init__(self, TACblock_ident:dict, ident:str, opcode:str, operands:str=None, defs:list=None, values:dict=None):
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
    def __init__(self):
        __aliases__ = []
    
    def __getattr__(self, key):
        if key in object.__getattribute__(self, "__aliases__"):
            aliased_key = self.__aliases__[key]
            return object.__getattribute__(self, aliased_key)
        else:
            return object.__getattribute__(self, key)

    def __setattr__(self, key, value):
        if key in object.__getattribute__(self, "__aliases__"):
            aliased_key = self.__aliases__[key]
            object.__setattr__(self, aliased_key, value)
        else:
            object.__setattr__(self, key, value)

class TAC_Base(Aliased):
    __internal_name__ = None
    __aliases__ = {}

    def __init__(self):
        self.block_ident = None
        self.stmt_ident = None
        self.arg_vars = []
        self.arg_vals = {}
        self.num_args = None

        self.res_var = None
        self.res_val = None

    def parse(self, raw_stmt: TAC_Statement):
        self.block_ident = raw_stmt.tac_block_id
        self.stmt_ident = raw_stmt.ident
        self.arg_vars = [x for x in raw_stmt.operands]
        self.arg_vals = {x: raw_stmt.values.get(x, None) for x in raw_stmt.operands}
        self.num_args = len(self.arg_vars)

        for i in range(self.num_args):
            var = self.arg_vars[i]
            object.__setattr__(self, "op{}_var".format(i+1), var)
            object.__setattr__(self, "op{}_val".format(i+1), self.arg_vals[var])

        self.res_var = raw_stmt.defs[0] if raw_stmt.defs else None
        self.res_val = raw_stmt.values.get(self.res_var, None)

    def set_op_val(self, state:SymbolicEVMState):
        for i in range(self.num_args):
            var = object.__getattr__(state, "op{}_var".format(i + 1))
            arg_val = object.__getattr__(state, "op{}_val".format(i + 1))
            val = arg_val or state.registers[var]
            object.__setattr__(self, "op{}_val".format(i + 1), val)

    def __str__(self):
        args_str = ''
        for arg in self.arg_vars:
            if not self.arg_vals.get(arg, None):
                args_str += "{}({})".format(arg, self.arg_vals[arg])
            else:
                args_str += "{}".format(arg)
            args_str += " "

        if not self.res_var:
            res_str = ""
        elif self.res_val:
            res_str = "{}({}) =".format(self.res_var, self.res_val)
        else:
            res_str = "{} =".format(self.res_var)

        return "{} {} {}".format(res_str, self.__internal_name__, args_str).strip()

class TAC_NoOperands(TAC_Base):
    pass

class TAC_NoOperandsNoRes(TAC_Base):
    pass

class TAC_Unary(TAC_Base):
    pass

class TAC_UnaryNoRes(TAC_Base):
    pass

class TAC_Binary(TAC_Base):
    pass

class TAC_BinaryNoRes(TAC_Base):
    pass

class TAC_Ternary(TAC_Base):
    pass

class TAC_TernaryNoRes(TAC_Base):
    pass

class TAC_Quaternary(TAC_Base):
    pass

class TAC_QuaternaryNoRes(TAC_Base):
    pass

class TAC_Quinary(TAC_Base):
    pass

class TAC_QuinaryNoRes(TAC_Base):
    pass

class TAC_Senary(TAC_Base):
    pass

class TAC_SenaryNoRes(TAC_Base):
    pass

class TAC_Septenary(TAC_Base):
    pass

class TAC_SeptenaryNoRes(TAC_Base):
    pass

class TAC_DynamicOps(Aliased):
    __internal_name__ = None
    __aliases__ = {}

    def __init__(self):
        self.block_ident = None
        self.stmt_ident = None
        self.arg_vars = []
        self.arg_vals = {}
        self.num_args = None
        self.res_vars = []
        self.res_vals = {}

    def parse(self, raw_stmt: TAC_Statement):
        self.block_ident = raw_stmt.tac_block_id
        self.stmt_ident = raw_stmt.ident
        self.arg_vars = [x for x in raw_stmt.operands]
        self.num_args = len(self.arg_vars)
        self.arg_vals = {x: raw_stmt.values.get(x, None) for x in raw_stmt.operands}
        self.res_vars = [x for x in raw_stmt.defs]
        self.res_vals = {x: raw_stmt.values.get(x, None) for x in raw_stmt.defs}

    def __str__(self):
        args_str = ''
        for arg in self.arg_vars:
            if not self.arg_vals.get(arg, None):
                args_str += "{}({})".format(arg, self.arg_vals[arg])
            else:
                args_str += "{}".format(arg)
            args_str += " "

        if not self.res_vars:
            res_str = ""
        else:
            res_str = ""
            for res in self.res_vars:
                if not self.res_vals.get(res, None):
                    res_str += "{}({})".format(res, self.res_vals[res])
                else:
                    res_str += "{}".format(res)
            res_str += " ="

        return "{} {} {}".format(res_str, self.__internal_name__, args_str).strip()


class TAC_DynamicOpsNoRes(TAC_DynamicOps):
    pass
