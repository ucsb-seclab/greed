
import z3

from SEtaac import utils
from SEtaac.utils import concrete, is_true, get_solver
from SEtaac.exceptions import ExternalData, SymbolicError, IntractablePath, VMException

from .base import TAC_NoOperandsNoRes, TAC_Septenary, TAC_Senary, TAC_UnaryNoRes, TAC_BinaryNoRes
from ..state import SymbolicEVMState


__all__ = ['TAC_Throw', 'TAC_Callprivate', 'TAC_Returnprivate', 'TAC_Phi', 'TAC_Const']

class TAC_Throw(TAC_NoOperandsNoRes):
    __internal_name__ = "THROW"
    def handle(self, state:SymbolicEVMState):
        pass

class TAC_Callprivate:
    __internal_name__ = "CALLPRIVATE"
    
    def __init__(self):
        self.args_var = []
        self.args_val = {}
        self.num_args = None
        self.res_vars = []
        self.res_vals = {}
        self.destination_var = None
        self.destination_val = None

    def parse(self, raw_stmt):
        self.arg_vars = [x for x in raw_stmt.operands]
        self.num_args = len(self.args_var)
        self.arg_vals = {x:raw_stmt.values.get(x, None) for x in raw_stmt.operands}
        self.res_vars = [x for x in raw_stmt.defs]
        self.res_vals = {x:raw_stmt.values.get(x, None) for x in raw_stmt.defs}
        
        self.destination_var = self.args_var[0]
        self.destination_val = raw_stmt.values.get(self.destination_var, None)

    def handle(self, state:SymbolicEVMState):
        pass

    def __str__(self):
        dest = self.destination_var if not self.destination_val else self.destination_var + '({})'.format(self.destination_val)
        
        args_str = ''
        for arg in self.arg_vars:
            if not self.arg_vals.get(arg, None):
                args_str += "{}({})".format(arg,self.arg_vals[arg])
            else:
                args_str += "{}".format(arg)
            args_str += " "
        
        ress_str = ''
        for res in self.res_vars:
            if not self.res_vals.get(res, None):
                ress_str += "{}({})".format(res,self.res_vals[res])
            else:
                ress_str += "{}".format(res)
            args_str += " "
        
        return "{} = {} {}".format(ress_str, self.__internal_name__, args_str)

class TAC_Returnprivate:
    __internal_name__ = "RETURNPRIVATE"
    def __init__(self):
        pass

    def parse(self, raw_stmt):
        self.arg_vars = [x for x in raw_stmt.operands]
        self.num_args = len(self.args_var)
        self.arg_vals = {x:raw_stmt.values.get(x, None) for x in raw_stmt.operands}        

    def __str__(self):        
        args_str = ''
        for arg in self.arg_vars:
            if not self.arg_vals.get(arg, None):
                args_str += "{}({})".format(arg,self.arg_vals[arg])
            else:
                args_str += "{}".format(arg)
            args_str += " "
        
        return "{} {}".format(self.__internal_name__, args_str)

class TAC_Phi:
    __internal_name__ = "PHI"
    def __init__(self):
        self.args_var = []
        self.args_val = {}
        self.num_args = None
        self.res_var = None
        self.res_val = None 
    
    def parse(self, raw_stmt):
        self.args_var = [x for x in raw_stmt.operands]
        self.num_args = len(self.args_var)
        self.args_val = {x:raw_stmt.values.get(x, None) for x in raw_stmt.operands}
        self.res_var = raw_stmt.defs[0]
    
    def __str__(self):
        args_str = ''
        for arg in self.args_var:
            args_str += "{} ".format(arg)
        return "PHI {}".format(args_str)

    def handle(self, state:SymbolicEVMState):
        pass

class TAC_Const:
    __internal_name__ = "CONST"

    def __init__(self):
        self.var = None
        self.val = None
    
    def parse(self, raw_stmt):
        self.var = raw_stmt.defs[0]
        self.val = raw_stmt.values[self.var]

    def __str__(self):
        return "{} = {}".format(self.var, self.val)

    def handle(self, state:SymbolicEVMState):
        succ = state.copy()

        succ.registers[self.var] = self.val

        succ.set_next_pc()
        return [succ]