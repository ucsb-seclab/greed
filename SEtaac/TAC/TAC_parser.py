import logging

from SEtaac import TAC
from SEtaac.TAC.base import TAC_RawStatement
from SEtaac.TAC.special_ops import TAC_Stop
from SEtaac.cfg import TAC_Block

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

        # inject a fake STOP statement to simplify the handling of CALLPRIVATE without successors
        # create fake STOP statement
        fake_raw_statement = TAC_RawStatement(TACblock_ident='fake_exit', ident='fake_exit', opcode='STOP')

        # parse raw statement
        stop = TAC_Stop()
        stop.parse(fake_raw_statement)

        # create fake block
        self._fake_exit_stmt = stop
        self._fake_exit_block = TAC_Block(block_id='fake_exit', statements=[stop])

    def parse(self, block_id) -> TAC_Block:

        stmts = []

        if block_id == "fake_exit":
            return self._fake_exit_block
        elif block_id not in self.TAC_code.keys():
            l.debug("Deadblock at {}".format(block_id))
            return None

        l.debug("Parsing block at {}".format(block_id))

        # If we have already parsed this, no need to parse it again :) 
        if block_id in self.TAC_code_cache.keys():
            return self.TAC_code_cache[block_id]

        # Create the specialized TAC statements
        for raw_tac_stmt in self.TAC_code[block_id]:
            # Look for the correspondent tac_op

            found = False
            for tac_op in TAC.__dict__.values():
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
                # raise TACparser_NO_OPS()

                # FIXME
                # This is just for debug, this shouldn't happen when we have all the
                # operations (we will raise the exception).
                stmts.append(raw_tac_stmt)

        bb = TAC_Block(stmts, block_id)

        # Save in cache the current parse ops.
        self.TAC_code_cache[block_id] = bb

        return bb
