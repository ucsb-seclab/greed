from SEtaac.state_plugins import SimStatePlugin


class SimStateGlobals(SimStatePlugin):

    def __init__(self, backer=None):
        super(SimStateGlobals, self).__init__()
        self._backer = backer if backer is not None else {}
        return

    def __getitem__(self, k):
        return self._backer[k]

    def __setitem__(self, k, v):
        self._backer[k] = v

    def __delitem__(self, k):
        del self._backer[k]

    def __contains__(self, k):
        return k in self._backer

    def keys(self):
        return self._backer.keys()

    def values(self):
        return self._backer.values()

    def items(self):
        return self._backer.items()

    def get(self, k, alt=None):
        return self._backer.get(k, alt)

    def pop(self, k, alt=None):
        return self._backer.pop(k, alt)
 
    def copy(self):
        new_backer = dict(self._backer)
        return SimStateGlobals(new_backer)

    def __str__(self):
        return ''.join(f"{k}:{v}" for k, v in self._backer.items())
