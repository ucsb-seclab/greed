import logging

from greed.state_plugins import SimStatePlugin

log = logging.getLogger(__name__)

OP_BEFORE = 0
OP_AFTER = 1

class SimStateHook(SimStatePlugin):
    """
    A plugin that allows hooking to be invoked on statements
    """

    def __init__(self, hook_stmt_ids=None, hook_stmt=None):
        super(SimStateHook, self).__init__()
        self.hook_stmt_ids = hook_stmt_ids if hook_stmt_ids else {OP_BEFORE: {}, OP_AFTER: {}}
        self.hook_stmt = hook_stmt if hook_stmt else {OP_BEFORE: {}, OP_AFTER: {}}

    def hook_at_stmt_id(self, stmt_id, func=None, when=OP_BEFORE, replace=False):
        """
        Hook at a statemnt with a given ID (i.e., PC)
        
        Args:
            stmt_id: The ID of the statement to hook.
            func: The function to call when the hook is invoked.
            when: Whether to hook before or after the statemnt.
            replace: Whether to replace the default handling of the statement. If set, the func should return state's successors.
        """

        if replace and when != OP_BEFORE:
            raise ValueError("When 'replace' is True, 'when' must be OP_BEFORE.")
        
        if not func:
            def justStop(simgr, state):
                log.warning("💥 Triggered hook at {}".format(state.pc))
                import ipdb; ipdb.set_trace()
            func = justStop

        if when not in self.hook_stmt_ids:
            self.hook_stmt_ids[when] = {}

        self.hook_stmt_ids[when][stmt_id] = (func, replace)


    def hook_at_stmt(self, stmt_name=None, func=None, when=OP_BEFORE, replace=False):
        """
        Hook at a statement with a given opcode name (e.g., CALL)
        
        Args:
            stmt_name: The name of the opcode name to hook.
            func: The function to call when the hook is triggered (default: ipdb.set_trace())
            when: Whether to hook before or after the statement
            replace: Whether to replace the default handling of the statement. If set, the func should return state's successors
        """

        if replace and when != OP_BEFORE:
            raise ValueError("When 'replace' is True, 'when' must be OP_BEFORE.")

        if not func:
            def justStop(simgr, state):
                log.warning("💥 Triggered hook at {}".format(state.pc))
                import ipdb; ipdb.set_trace()

            func = justStop

        if when not in self.hook_stmt:
            self.hook_stmt[when] = {}

        self.hook_stmt[when][stmt_name] = (func, replace)

    def copy(self):
        """
        Deep copy this state plugin
        """

        new_hook_stmt_ids = dict(self.hook_stmt_ids)
        new_hook_stmt = dict(self.hook_stmt)
        return SimStateHook(new_hook_stmt_ids, new_hook_stmt)
