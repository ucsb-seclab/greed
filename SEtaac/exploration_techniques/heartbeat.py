import logging
import os
import tempfile

from . import ExplorationTechnique

log = logging.getLogger(__name__)


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

    def check_successors(self, simgr, successors):
        self.beat_cnt += 1
        self.steps_cnt += 1
        if self.beat_cnt == self.beat_interval:
            log.info("Exploration is alive <3. Step {}".format(self.steps_cnt))
            log.info("    Succs are: {}".format(successors))
            self.beat_cnt = 0
            if not os.path.isfile(self.heart_beat_file):
                log.info("HeartBeat stopped, need help? </3")
                import ipdb
                ipdb.set_trace()

        return successors
