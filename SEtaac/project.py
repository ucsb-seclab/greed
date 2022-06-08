from SEtaac.cfg import CFG
from SEtaac.simulation_manager import SimulationManager


class Project(object):
    def __init__(self, code):
        self.code = code
        self._cfg = None
        self._simgr = None

        # todo: we need the gigahorse analysis folder here

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