
import logging
import os
from . import ExplorationTechnique

l = logging.getLogger("HeartBeat")
l.setLevel(logging.INFO)

class HeartBeat(ExplorationTechnique):
    def __init__(self, beat_interval=100):
        super(DFS,self).__init__()
        self.stop_heart_beat_file = "/tmp/stop_heartbeat.txt"
        self.beat_interval = beat_interval
        self.beat_cnt = 0
        self.steps_cnt = 0

    def setup(self, simgr):
        return

    def check_stashes(self, stashes, stash='active'):
        return stashes

    def check_state(self, state):
        return state

    def check_successors(self, successors):
        self.beat_cnt += 1
        self.steps_cnt += 1
        if self.beat_cnt == self.beat_interval:
            l.info("Exploration is alive <3. Step {}".format(self.steps_cnt)) 
            l.info("    Succs are: {}".format(successors))
            self.beat_cnt = 0
            if os.path.isfile(self.stop_heart_beat_file):
                l.info("HeartBeat stopped, need help? </3")
                import ipdb; ipdb.set_trace()
                
    def is_complete(self,simgr, stash='active'):
        return True