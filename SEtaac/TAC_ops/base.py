from SEtaac.state import SymbolicEVMState

# This is the object exported from Gigahorse
class TAC_RawStatement:
    __name__ = "TAC_Statement"
    __internal_name__ = ""
    def __init__(self, TACblock_ident:str, ident:str, opcode:str, operands:str=None, defs:list=None, values:dict=None):
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

class TAC_Statement(Aliased):
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
        self.num_ress = None

    def parse(self, raw_stmt: TAC_RawStatement):
        self.block_ident = raw_stmt.tac_block_id
        self.stmt_ident = raw_stmt.ident

        self.arg_vars = [x for x in raw_stmt.operands]
        self.arg_vals = {x: raw_stmt.values.get(x, None) for x in raw_stmt.operands}
        self.num_args = len(self.arg_vars)
        # cast arg_vals to int
        self.arg_vals = {x: int(v, 16) if v else v for x, v in self.arg_vals.items()}

        for i in range(self.num_args):
            var = self.arg_vars[i]
            object.__setattr__(self, "arg{}_var".format(i+1), var)
            object.__setattr__(self, "arg{}_val".format(i+1), self.arg_vals[var])

        self.res_vars = [x for x in raw_stmt.defs]
        self.res_vals = {x: raw_stmt.values.get(x, None) for x in raw_stmt.defs}
        self.num_ress = len(self.res_vars)
        # cast res_vals to int
        self.res_vals = {x: int(v, 16) if v else v for x, v in self.res_vals.items()}

        for i in range(self.num_ress):
            var = self.res_vars[i]
            object.__setattr__(self, "res{}_var".format(i+1), var)
            object.__setattr__(self, "res{}_val".format(i+1), self.res_vals[var])

    def set_arg_val(self, state:SymbolicEVMState):
        for i in range(self.num_args):
            var = self.arg_vars[i]
            arg_val = self.arg_vals[var]
            val = state.registers[var] if arg_val is None else arg_val
            self.arg_vals[var] = val

    def __str__(self):
        args_str = ''
        for arg in self.arg_vars:
            args_str += "{}".format(arg)
            args_str += " "

        if not self.res_vars:
            res_str = ""
        else:
            res_str = ""
            for res in self.res_vars:
                res_str += "{}".format(res)
            res_str += " ="

        return "{} {} {}".format(res_str, self.__internal_name__, args_str).strip()

    def __repr__(self):
        return str(self)


# def handler(func):
#     """
#     Decorator that executes the basic handler functionalities.
#     """
#     def wrap(*args, **kwargs):
#         successors = func(*args, **kwargs)
#         return successors
#
#     return wrap