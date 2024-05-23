from typing import NamedTuple, TYPE_CHECKING
from enum import Enum

if TYPE_CHECKING:
    from greed.function import TAC_Function

class SafeMathFunc(Enum):
    ADD = 'add'
    ADD_SIGNED = 'add_signed'
    SUB = 'sub'
    SUB_SIGNED = 'sub_signed'
    MUL = 'mul'
    MUL_SIGNED = 'mul_signed'
    DIV = 'div'
    SDIV = 'sdiv'
    MOD = 'mod'
    SMOD = 'smod'

class SafeMathFuncReport(NamedTuple):
    """
    A report that contains information about an identified SAFEMATH function.

    Attributes:
    -----------
    func_kind: The type of SAFEMATH function identified.
    func: The function.
    first_arg_at_start:  For order-dependent functions (SUB, DIV), indicates whether the
        first argument to the function is the first argument to the operator.
    """
    func_kind: SafeMathFunc
    func: 'TAC_Function'
    first_arg_at_start: bool
