
import logging

from SEtaac.exploration_techniques import ExplorationTechnique


LOGGING_FORMAT = "%(levelname)s | %(name)s | %(message)s"
logging.basicConfig(level=logging.INFO, format=LOGGING_FORMAT)
log = logging.getLogger("GuardedBlockChecker")
log.setLevel(logging.INFO)

class GuardedBlockChecker(ExplorationTechnique):
    def __init__(self, checked_blocks:dict):
        super(GuardedBlockChecker, self).__init__()
        self.checked_blocks_ids = [block.id for block in checked_blocks]
        self.checked_blocks_covered = set()
        self.deadended_checked = set()
        self.done = False
        

    def check_stashes(self, simgr, stashes, stash='active'):
        if len(stashes['deadended']) > 1:
            for deadended_state in stashes['deadended']:
                # Check only new deadended states
                if deadended_state not in self.deadended_checked:
                    for stmt in deadended_state.trace:
                        if stmt.block_id in self.checked_blocks_ids:
                            log.debug(f"   >>>Covered guarded basic block at {stmt.block_id}")
                            self.checked_blocks_covered.add(stmt.block_id)  
        if len(self.checked_blocks_covered) == len(self.checked_blocks_ids):
            self.done = True
        
        return stashes
            

    def is_complete(self, simgr, stash='active'):
        if self.done or len(simgr.stashes['active']) == 0:
            return True
        else:
            return False
