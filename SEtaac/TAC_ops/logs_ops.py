from .base import TAC_BinaryNoRes, TAC_TernaryNoRes, TAC_QuaternaryNoRes, TAC_QuinaryNoRes, TAC_SenaryNoRes
                  
from ..state import SymbolicEVMState

__all__ = [
    'TAC_Log0','TAC_Log1','TAC_Log2','TAC_Log3','TAC_Log4'
]


"""
aka. "EVENTS"
0xa0 ... 0xa4, 32/64/96/128/160 + len(data) gas
a. Opcodes LOG0...LOG4 are added, takes 2-6 stack arguments
        MEMSTART MEMSZ (TOPIC1) (TOPIC2) (TOPIC3) (TOPIC4)
b. Logs are kept track of during tx execution exactly the same way as selfdestructs
   (except as an ordered list, not a set).
   Each log is in the form [address, [topic1, ... ], data] where:
   * address is what the ADDRESS opcode would output
   * data is self.memory[MEMSTART: MEMSTART + MEMSZ]
   * topics are as provided by the opcode
c. The ordered list of logs in the transaction are expressed as [log0, log1, ..., logN].
"""


class TAC_Log0(TAC_BinaryNoRes):
    __internal_name__ = "LOG0"
    __aliases__ = {
                   'offset_var': 'op1_var', 'offset_val': 'op1_val',
                   'size_var'  : 'op2_var', 'size_var'  : 'op2_val'
                  }

    def handle(self, state:SymbolicEVMState):
        succ = state.copy()
        arg1 = succ.registers[self.op1_var]
        arg2 = succ.registers[self.op2_var]

        mstart, msz = arg1, arg2
        succ.memory.extend(mstart, msz)
        # Ignore external effects...
        # depth = 0
        # topics = []

        succ.set_next_pc()
        return [succ]

class TAC_Log1(TAC_TernaryNoRes):
    __internal_name__ = "LOG1"
    __aliases__ = {
                   'offset_var'  : 'op1_var'  , 'offset_val'  : 'op1_val',
                   'size_var'    : 'op2_var'  , 'size_var'    : 'op2_val',
                   'topic_var'   : 'op3_var'  , 'topic_val'   : 'op3_val'
                   }

    def handle(self, state:SymbolicEVMState):
        succ = state.copy()
        arg1 = succ.registers[self.op1_var]
        arg2 = succ.registers[self.op2_var]
        arg3 = succ.registers[self.op3_var]

        mstart, msz = arg1, arg2
        succ.memory.extend(mstart, msz)
        # Ignore external effects...
        # depth = 1
        # topics = [arg3]

        succ.set_next_pc()
        return [succ]

class TAC_Log2(TAC_QuaternaryNoRes):
    __internal_name__ = "LOG2"
    __aliases__ = {
                   'offset_var'  : 'op1_var'  , 'offset_val'  : 'op1_val',
                   'size_var'    : 'op2_var'  , 'size_var'    : 'op2_val',
                   'topic1_var'  : 'op3_var'  , 'topic1_val'  : 'op3_val',
                   'topic2_var'  : 'op4_var'  , 'topic2_val'  : 'op4_val'
                   }

    def handle(self, state:SymbolicEVMState):
        succ = state.copy()
        arg1 = succ.registers[self.op1_var]
        arg2 = succ.registers[self.op2_var]
        arg3 = succ.registers[self.op3_var]
        arg4 = succ.registers[self.op4_var]

        mstart, msz = arg1, arg2
        succ.memory.extend(mstart, msz)
        # Ignore external effects...
        # depth = 2
        # topics = [arg3, arg4]

        succ.set_next_pc()
        return [succ]

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
        succ = state.copy()
        arg1 = succ.registers[self.op1_var]
        arg2 = succ.registers[self.op2_var]
        arg3 = succ.registers[self.op3_var]
        arg4 = succ.registers[self.op4_var]
        arg5 = succ.registers[self.op5_var]

        mstart, msz = arg1, arg2
        succ.memory.extend(mstart, msz)
        # Ignore external effects...
        # depth = 3
        # topics = [arg3, arg4, arg5]

        succ.set_next_pc()
        return [succ]

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
        succ = state.copy()
        arg1 = succ.registers[self.op1_var]
        arg2 = succ.registers[self.op2_var]
        arg3 = succ.registers[self.op3_var]
        arg4 = succ.registers[self.op4_var]
        arg5 = succ.registers[self.op5_var]
        arg6 = succ.registers[self.op6_var]

        mstart, msz = arg1, arg2
        succ.memory.extend(mstart, msz)
        # Ignore external effects...
        # depth = 4
        # topics = [arg3, arg4, arg5, arg6]

        succ.set_next_pc()
        return [succ]