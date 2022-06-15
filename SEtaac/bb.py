from SEtaac.TAC_ops.base import TAC_Statement
from SEtaac.TAC_ops.gigahorse_ops import TAC_Nop


class TAC_Block(object):
    def __init__(self, statements, block_id):
        self.ident = block_id
        self.statements = statements
        self.function = None
        # WARNING: Gigahorse sometimes creates empty 
        #          basic blocks (i.e., no statements)
        #          we patch such blocks with a fake NOP
        if len(self.statements) == 0:
            # inject a fake NOP statement to simplify the handling of empty blocks
            # create fake raw statement
            fake_raw_statement = TAC_Statement(TACblock_ident=block_id, ident=block_id+'_fake_stmt', opcode='NOP')

            # parse raw statement
            nop = TAC_Nop()
            nop.parse(fake_raw_statement)

            self.statements.append(nop)
            self.first_ins = nop

        self.first_ins = self.statements[0]
        
        # This keep a dictionary from statement id to statement.
        self._statement_at = {s.stmt_ident:s for s in self.statements}

    def __str__(self):
        return "Block at {}".format(self.ident)

    def __repr__(self):
        return str(self)