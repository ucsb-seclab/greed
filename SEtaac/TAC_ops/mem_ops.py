
import z3

from SEtaac import utils
from SEtaac.exceptions import SymbolicError
from SEtaac.utils import concrete

from .base import TAC_BinaryNoRes, TAC_NoOperands, TAC_Unary
                  
from ..state import SymbolicEVMState

__all__ = ['TAC_Mstore', 'TAC_Mstore8', 'TAC_Mload', 'TAC_Sload', 'TAC_Sstore', 'TAC_Msize']

class TAC_Mstore(TAC_BinaryNoRes):
    __internal_name__ = "MSTORE"
    __aliases__ = {
                   'offset_var' : 'op1_var', 'offset_val' : 'op1_val',
                   'value_var'  : 'op2_var', 'value_val'  : 'op2_val'
                  }

    def handle(self, state:SymbolicEVMState):
        pass

class TAC_Mstore8(TAC_BinaryNoRes):
    __internal_name__ = "MSTORE8"
    __aliases__ = {
                   'offset_var' : 'op1_var', 'offset_val' : 'op1_val',
                   'value_var'  : 'op2_var', 'value_val'  : 'op2_val'
                  }

    def handle(self, state:SymbolicEVMState):
        pass

class TAC_Mload(TAC_Unary):
    __internal_name__ = "MLOAD"
    __aliases__ = {
                   'offset_var' : 'op1_var', 'offset_val' : 'op1_val',
                   'value_var'  : 'res_var', 'value_val'  : 'res_val'
                  }

    def handle(self, state:SymbolicEVMState):
        pass

class TAC_Sload(TAC_Unary):
    __internal_name__ = "SLOAD"
    __aliases__ = {
                   'key_var'    : 'op1_var', 'key_val'    : 'op1_val',
                   'value_var'  : 'res_var', 'value_val'  : 'res_val'
                  }

    def handle(self, state:SymbolicEVMState):
        pass

class TAC_Sstore(TAC_BinaryNoRes):
    __internal_name__ = "SSTORE"
    __aliases__ = {
                   'key_var'    : 'op1_var', 'key_val'    : 'op1_val',
                   'value_var'  : 'op2_var', 'value_val'  : 'op2_val'
                  }

    def handle(self, state:SymbolicEVMState):
        pass

class TAC_Msize(TAC_NoOperands):
    __internal_name__ = "MSIZE"
    __aliases__ = {
                   'size_var'  : 'res_var', 'size_val'  : 'res_val'
                  }

    def handle(self, state:SymbolicEVMState):
        pass