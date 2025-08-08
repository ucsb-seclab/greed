from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from greed.state import SymbolicEVMState


class SimStatePlugin:
    """
    Interface for SimState plugins.
    """
    state: "SymbolicEVMState"

    def __init__(self):
        self.state = None
        return
    
    def set_state(self, state: "SymbolicEVMState"):
        self.state = state

    def copy(self):
        raise Exception("Not implemented")
