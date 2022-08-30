from SEtaac.TAC.base import TAC_Statement

from SEtaac.state import SymbolicEVMState

__all__ = [
    'TAC_Log0', 'TAC_Log1', 'TAC_Log2', 'TAC_Log3', 'TAC_Log4'
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


class TAC_Log(TAC_Statement):
    __internal_name__ = "LOG"
    __aliases__ = {
        'offset_var': 'arg1_var', 'offset_val': 'arg1_val',
        'size_var': 'arg2_var', 'size_val': 'arg2_val'
    }

    @TAC_Statement.handler_with_side_effects
    def handle(self, state: SymbolicEVMState):
        state.set_next_pc()
        return [state]


class TAC_Log0(TAC_Log):
    __internal_name__ = "LOG0"
    __aliases__ = {
        'offset_var': 'arg1_var', 'offset_val': 'arg1_val',
        'size_var': 'arg2_var', 'size_val': 'arg2_val'
    }


class TAC_Log1(TAC_Log):
    __internal_name__ = "LOG1"
    __aliases__ = {
        'offset_var': 'arg1_var', 'offset_val': 'arg1_val',
        'size_var': 'arg2_var', 'size_val': 'arg2_val',
        'topic_var': 'arg3_var', 'topic_val': 'arg3_val'
    }


class TAC_Log2(TAC_Log):
    __internal_name__ = "LOG2"
    __aliases__ = {
        'offset_var': 'arg1_var', 'offset_val': 'arg1_val',
        'size_var': 'arg2_var', 'size_val': 'arg2_val',
        'topic1_var': 'arg3_var', 'topic1_val': 'arg3_val',
        'topic2_var': 'arg4_var', 'topic2_val': 'arg4_val'
    }


class TAC_Log3(TAC_Log):
    __internal_name__ = "LOG3"
    __aliases__ = {
        'offset_var': 'arg1_var', 'offset_val': 'arg1_val',
        'size_var': 'arg2_var', 'size_val': 'arg2_val',
        'topic1_var': 'arg3_var', 'topic1_val': 'arg3_val',
        'topic2_var': 'arg4_var', 'topic2_val': 'arg4_val',
        'topic3_var': 'arg5_var', 'topic3_val': 'arg5_val'
    }


class TAC_Log4(TAC_Log):
    __internal_name__ = "LOG4"
    __aliases__ = {
        'offset_var': 'arg1_var', 'offset_val': 'arg1_val',
        'size_var': 'arg2_var', 'size_val': 'arg2_val',
        'topic1_var': 'arg3_var', 'topic1_val': 'arg3_val',
        'topic2_var': 'arg4_var', 'topic2_val': 'arg4_val',
        'topic3_var': 'arg5_var', 'topic3_val': 'arg5_val',
        'topic4_var': 'arg6_var', 'topic4_val': 'arg6_val'
    }
