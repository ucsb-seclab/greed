import logging

from greed.state_plugins import SimStatePlugin

log = logging.getLogger(__name__)

OP_BEFORE = 0
OP_AFTER = 1


class SimStateInspect(SimStatePlugin):

    def __init__(self, breakpoints_stmt_ids=None, breakpoints_stmt=None):
        super(SimStateInspect, self).__init__()
        self.breakpoints_stmt_ids = breakpoints_stmt_ids if breakpoints_stmt_ids is not None else {}
        self.breakpoints_stmt = breakpoints_stmt if breakpoints_stmt is not None else {}
        return

    def stop_at_stmt_id(self, stmt_id=None, func=None, when=OP_BEFORE):
        if not func:
            def justStop(simgr, state):
                log.warning("💥 Triggered breakpoint at {}".format(state.pc))
                import ipdb; ipdb.set_trace()
            func = justStop
        self.breakpoints_stmt_ids[stmt_id] = func

    def stop_at_stmt(self, stmt_name=None, func=None, when=OP_BEFORE):
        if not func:
            def justStop(simgr, state):
                import ipdb
                ipdb.set_trace()
            func = justStop
        self.breakpoints_stmt[stmt_name] = func

    def copy(self):
        new_breakpoints_stmt_ids = dict(self.breakpoints_stmt_ids)
        new_breakpoints_stmt = dict(self.breakpoints_stmt)
        return SimStateInspect(new_breakpoints_stmt_ids, new_breakpoints_stmt)
