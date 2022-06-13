

import logging

class TAC_Function:
    def __init__(self, id:str, name:str, public:bool, blocks:list, arguments:list):
        self.id = id
        self.name = name
        self.public = public 
        self.blocks = blocks
        self.arguments = arguments
        self.cfg = None
    
