import z3

from SEtaac import utils
from SEtaac.exceptions import SymbolicError
from SEtaac.utils import concrete

from .base import TAC_BinaryNoRes, TAC_TernaryNoRes, TAC_QuaternaryNoRes, TAC_QuinaryNoRes, TAC_SenaryNoRes
                  
from ..state import SymbolicEVMState

__all__ = [
    'TAC_Log0','TAC_Log1','TAC_Log2','TAC_Log3','TAC_Log4'
]


class TAC_Log0(TAC_BinaryNoRes):
    __internal_name__ = "LOG0"
    __aliases__ = {
                   'offset_var': 'op1_var', 'offset_val': 'op1_val',
                   'size_var'  : 'op2_var', 'size_var'  : 'op2_val'
                  }

    def handle(self, state:SymbolicEVMState):
        pass

class TAC_Log1(TAC_TernaryNoRes):
    __internal_name__ = "LOG1"
    __aliases__ = {
                   'offset_var'  : 'op1_var'  , 'offset_val'  : 'op1_val',
                   'size_var'    : 'op2_var'  , 'size_var'    : 'op2_val',
                   'topic_var'   : 'op3_var'  , 'topic_val'   : 'op3_val'
                   }

    def handle(self, state:SymbolicEVMState):
        pass

class TAC_Log2(TAC_QuaternaryNoRes):
    __internal_name__ = "LOG2"
    __aliases__ = {
                   'offset_var'  : 'op1_var'  , 'offset_val'  : 'op1_val',
                   'size_var'    : 'op2_var'  , 'size_var'    : 'op2_val',
                   'topic1_var'  : 'op3_var'  , 'topic1_val'  : 'op3_val',
                   'topic2_var'  : 'op4_var'  , 'topic2_val'  : 'op4_val'
                   }

    def handle(self, state:SymbolicEVMState):
        pass

class TAC_Log3(TAC_QuinaryNoRes):
    __internal_name__ = "LOG3"
    __aliases__ = {
                   'offset_var'  : 'op1_var'  , 'offset_val'  : 'op1_val',
                   'size_var'    : 'op2_var'  , 'size_var'    : 'op2_val',
                   'topic1_var'  : 'op3_var'  , 'topic1_val'  : 'op3_val',
                   'topic2_var'  : 'op4_var'  , 'topic2_val'  : 'op4_val',
                   'topic3_var'  : 'op5_var'  , 'topic3_val'  : 'op5_val'
                   }

    def handle(self, state:SymbolicEVMState):
        pass

class TAC_Log4(TAC_SenaryNoRes):
    __internal_name__ = "LOG4"
    __aliases__ = {
                   'offset_var'  : 'op1_var'  , 'offset_val'  : 'op1_val',
                   'size_var'    : 'op2_var'  , 'size_var'    : 'op2_val',
                   'topic1_var'  : 'op3_var'  , 'topic1_val'  : 'op3_val',
                   'topic2_var'  : 'op4_var'  , 'topic2_val'  : 'op4_val',
                   'topic3_var'  : 'op5_var'  , 'topic3_val'  : 'op5_val',
                   'topic4_var'  : 'op6_var'  , 'topic4_val'  : 'op6_val'
                   }

    def handle(self, state:SymbolicEVMState):
        pass