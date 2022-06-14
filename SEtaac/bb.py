

class TAC_Block(object):
    def __init__(self, statements, block_id):
        self.ident = block_id
        self.statements = statements
        
        # WARNING: Gigahorse sometimes creates empty 
        #          basic blocks (i.e., no statements)
        #          We'll keep as of now.
        if len(statements) > 0:
            self.first_ins = statements[0]
        else:
            self.first_ins = None