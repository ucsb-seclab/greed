
class SimStatePlugin:
    """
    Interface for SimState plugins.
    """
    def __init__(self):
        self.state = None
        return
    
    def set_state(self, state):
        self.state = state

    def copy(self):
        raise Exception("Not implemented")
