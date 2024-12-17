import logging

from greed.state_plugins import SimStatePlugin
import greed.options as opt

log = logging.getLogger(__name__)

class SimStateInspect(SimStatePlugin):
    """
    A plugin that allows for breakpoints to be set on statements.
    """

    def __init__(self, breakpoints_stmt_ids=None, breakpoints_stmt=None):
        super(SimStateInspect, self).__init__()
        self.breakpoints_stmt_ids = breakpoints_stmt_ids if breakpoints_stmt_ids is not None else {}
        self.breakpoints_stmt = breakpoints_stmt if breakpoints_stmt is not None else {}
        return

    def stop_at_stmt_id(self, stmt_id=None, func=None, when=opt.OP_BEFORE):
        """
        Stop at a statement with a given ID (i.e., PC)
        Args:
            stmt_id: The ID of the statement to stop at.
            func: The function to call when the breakpoint is hit.
            when: Whether to stop before or after the statement.

        The default function if none is provided is:
        '''
        def justStop(simgr, state):
            log.warning("💥 Triggered breakpoint at {}".format(state.pc))
            import ipdb; ipdb.set_trace()
        '''
        """
        if not func:
            def justStop(simgr, state):
                log.warning("💥 Triggered breakpoint at {}".format(state.pc))
                import ipdb; ipdb.set_trace()
            func = justStop

        if when not in self.breakpoints_stmt_ids:
            self.breakpoints_stmt_ids[when] = {}
            
        self.breakpoints_stmt_ids[when][stmt_id] = func

    def stop_at_stmt(self, stmt_name=None, func=None, when=opt.OP_BEFORE):
        """
        Stop at a statement with a given name (e.g., CALL)
        Args:
            stmt_name: The name of the statement to stop at.
            func: The function to call when the breakpoint is hit (default: ipdb.set_trace())
            when: Whether to stop before or after the statement.
        """
        if not func:
            def justStop(simgr, state):
                import ipdb
                ipdb.set_trace()
            func = justStop

        if when not in self.breakpoints_stmt:
            self.breakpoints_stmt[when] = {}

        self.breakpoints_stmt[when][stmt_name] = func

    def copy(self):
        """
        Deep copy this state plugin.
        """
        new_breakpoints_stmt_ids = dict(self.breakpoints_stmt_ids)
        new_breakpoints_stmt = dict(self.breakpoints_stmt)
        return SimStateInspect(new_breakpoints_stmt_ids, new_breakpoints_stmt)
