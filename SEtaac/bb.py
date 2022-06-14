

class TAC_Block(object):
    def __init__(self, statements, block_id):
        self.ident = block_id
        self.statements = statements
        self.first_ins = statements[0]