
from TAC_ops import *

'''
The TACparser takes one block of TAC_Statement(s) and create the 
specialized TAC_ops that are eventually feeded to the symb executor.
'''
class TACparser:
    def __init__(self, TAC_code):
        self.TAC_code = TAC_code

    def parse(self, block_id):
        stmts = []
        for tac_stmt in self.TAC_code[block_id]:
            stmts.append()