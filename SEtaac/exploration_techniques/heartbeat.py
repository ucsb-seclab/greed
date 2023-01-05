import logging
import os
import tempfile

from . import ExplorationTechnique

log = logging.getLogger(__name__)
#log.setLevel(logging.INFO)

class HeartBeat(ExplorationTechnique):
    """
    This Exploration technique implements a Classic heartbeat.
    The heartbeat file will be logged during __init__.
    Delete such file to stop the heartbeat and get an ipdb shell.
    """
    def __init__(self, beat_interval=100, show_op=False):
        super(HeartBeat, self).__init__()
        self.heart_beat_file = tempfile.NamedTemporaryFile(prefix='SEtaac_heartbeat_', delete=False).name
        log.info(f"Heartbeat file: {self.heart_beat_file} (delete to stop heartbeat)")
        self.beat_interval = beat_interval
        self.beat_cnt = 0
        self.steps_cnt = 0
        self.show_op = show_op
 
    def check_successors(self, simgr, successors):
        self.beat_cnt += 1
        self.steps_cnt += 1
        if self.beat_cnt == self.beat_interval:
            log.info("Exploration is alive <3. Step {}".format(self.steps_cnt))
            log.info(f"Simgr: {simgr} (active: {simgr.active})")
            if self.show_op:
                log.info(f"State: {simgr.active[0]} (curr_stmt: {simgr.active[0].curr_stmt})")
            self.beat_cnt = 0
            if not os.path.isfile(self.heart_beat_file):
                log.info("HeartBeat stopped, need help? </3")
                import ipdb
                ipdb.set_trace()
        
        return successors
    
    def change_beat(self, new_beat_interval):
        self.beat_interval = new_beat_interval
        self.beat_cnt = 0
