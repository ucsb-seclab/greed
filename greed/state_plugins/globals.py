from copy import deepcopy

from greed.state_plugins import SimStatePlugin


class SimStateGlobals(SimStatePlugin):
    """
    A plugin that allows for global variables to be stored in the state.
    This will act like a dictionary.
    """
    def __init__(self, backer=None):
        super(SimStateGlobals, self).__init__()
        self._backer = backer if backer is not None else dict()
        return

    def __getitem__(self, k):
        """
        Get the value of a global variable.
        Args:
            k: The name of the global variable.
        """
        return self._backer[k]

    def __setitem__(self, k, v):
        """
        Set the value of a global variable.
        Args:
            k: The name of the global variable.
            v: The value of the global variable.
        """
        self._backer[k] = v

    def __delitem__(self, k):
        """
        Delete a global variable.
        Args:
            k: The name of the global variable.
        """
        del self._backer[k]

    def __contains__(self, k):
        """
        Check if a global variable exists.
        Args:
            k: The name of the global variable.
        """
        return k in self._backer

    def keys(self):
        """
        Get the names of all global variables.
        """
        return self._backer.keys()

    def values(self):
        """
        Get the values of all global variables.
        """
        return self._backer.values()

    def items(self):
        """
        Get the names and values of all global variables.
        """
        return self._backer.items()

    def get(self, k, alt=None):
        """
        Get the value of a global variable, or return an alternative value.
        Args:
            k: The name of the global variable.
            alt: The alternative value to return if the global variable does not exist.
        """
        return self._backer.get(k, alt)

    def pop(self, k, alt=None):
        """
        Get the value of a global variable, and remove it from the state.
        Args:
            k: The name of the global variable.
            alt: The alternative value to return if the global variable does not exist.
        """
        return self._backer.pop(k, alt)
 
    def copy(self):
        """
        Get a deep-copy of this plugin.
        """
        new_backer = deepcopy(self._backer)
        return SimStateGlobals(new_backer)

    def __str__(self):
        return ''.join(f"{k}:{v}" for k, v in self._backer.items())
