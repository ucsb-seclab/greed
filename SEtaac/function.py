
import logging

class TAC_Function:
    def __init__(self, id:str, name:str, public:bool, blocks:list, arguments:list):
        self.id = id
        self.name = name
        self.public = public 
        self.blocks = blocks
        self.arguments = arguments
        self.cfg = None
        self.calls = self._get_calls()
    
    def _get_calls(self):
        internal_calls = []
        for bb in self.blocks:
            for s in bb.statements:
                if s.__internal_name__ == "CALLPRIVATE":
                    internal_calls.append(s.arg_vals[s.arg_vars[0]])
        return internal_calls
