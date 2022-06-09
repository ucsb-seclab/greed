
import logging 


from .exceptions import TACparser_NO_OPS
from . import TAC_ops

l = logging.getLogger("tac_parser")
l.setLevel(logging.INFO)

'''
The TACparser takes one block of TAC_Statement(s) and create the 
specialized TAC_ops that are eventually feeded to the symb executor.
'''
class TACparser:
    def __init__(self, TAC_code):
        self.TAC_code = TAC_code
        
        # Keep here the list of already parsed "raw" TAC_Statement
        self.TAC_code_cache = {}

    def parse(self, block_id):
        stmts = []
        
        # If we have already parsed this, no need to parse it again :) 
        if block_id in self.TAC_code_cache.keys():
            return self.TAC_code_cache[block_id]

        # Create the specialized TAC statements
        for raw_tac_stmt in self.TAC_code[block_id]:
            # Look for the correspondent tac_op
            
            found = False
            for tac_op in TAC_ops.__dict__.values():
                # FIXME HACK 
                # Maybe let's do a better import from TAC_ops
                if "type" not in str(type(tac_op)):
                    continue
                # If opcode matches, let's parse it! 
                if raw_tac_stmt.opcode == tac_op.__internal_name__:
                    # Create a new instance of this TAC_op
                    new_tac_op = tac_op.__new__(tac_op)
                    # Parse it! 
                    new_tac_op.parse(raw_tac_stmt)
                    # Add it to the parsed statements
                    stmts.append(new_tac_op)
                    found = True
                    break
            if not found:
                l.critical("Could not find a TAC_ops for TAC_Statement {}".format(raw_tac_stmt.opcode))
                #raise TACparser_NO_OPS()

                # This is just for debug, this shouldn't happen when we have all the
                # operations (we will raise the exception).
                stmts.append(raw_tac_stmt)
        
        # Save in cache the current parse ops.
        self.TAC_code_cache[block_id] = stmts.copy()
        
        return stmts
