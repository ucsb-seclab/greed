import logging
import os
import tempfile

from . import ExplorationTechnique

log = logging.getLogger(__name__)
#log.setLevel(logging.INFO)

from utils import bcolors

class HeartBeat(ExplorationTechnique):
    """
    This Exploration technique implements a Classic heartbeat.
    The heartbeat file will be logged during __init__.
    Delete such file to stop the heartbeat and get an ipdb shell.
    """
    def __init__(self, beat_interval=100):
        super(HeartBeat, self).__init__()
        self.heart_beat_file = tempfile.NamedTemporaryFile(prefix='SEtaac_heartbeat_', delete=False).name
        log.info(f"Heartbeat file: {self.heart_beat_file} (delete to stop heartbeat)")
        self.beat_interval = beat_interval
        self.beat_cnt = 0
        self.steps_cnt = 0

        self.check_state_warning_printed = False

    def check_state(self, simgr, state):
        if not self.check_state_warning_printed:
            log.fatal("{bcolors.YELLOWBG}Heartbeat is checking is_sat() for every state{bcolors.ENDC}")
            self.check_state_warning_printed = True
        state.solver.is_sat()
    
    def check_successors(self, simgr, successors):
        self.beat_cnt += 1
        self.steps_cnt += 1
        if self.beat_cnt == self.beat_interval:
            log.info("Exploration is alive <3. Step {}".format(self.steps_cnt))
            log.info(f"Simgr: {simgr} (active: {simgr.active})")
            self.beat_cnt = 0
            if not os.path.isfile(self.heart_beat_file):
                log.info("HeartBeat stopped, need help? </3")
                import ipdb
                ipdb.set_trace()
        
        return successors
    
    def change_beat(self, new_beat_interval):
        self.beat_interval = new_beat_interval
        self.beat_cnt = 0
