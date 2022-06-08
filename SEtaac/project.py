from SeTAC.cfg import CFG
from SeTAC.simulation_manager import SimulationManager


class Project(object):
    def __init__(self, code):
        self.code = code
        self._cfg = None
        self._simgr = None

    @property
    def cfg(self):
        if not self._cfg:
            self._cfg = CFG()
        return self._cfg

    @property
    def simgr(self):
        if not self._simgr:
            self._simgr = SimulationManager()
        return self._simgr