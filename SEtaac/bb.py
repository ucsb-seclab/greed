

class TAC_Block(object):
    def __init__(self, statements, block_id):
        self.ident = block_id
        self.statements = statements
        self.function = None
        # WARNING: Gigahorse sometimes creates empty 
        #          basic blocks (i.e., no statements)
        #          We'll keep as of now.
        if len(statements) > 0:
            self.first_ins = statements[0]
        else:
            self.first_ins = None
        
        # This keep a dictionary from statement id to statement.
        self._statement_at = {s.stmt_id:s for s in self.statements}

        
        
        
