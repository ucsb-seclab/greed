

__all__ = ['TAC_Jump', 'TAC_Jumpi']

class TAC_Jump:
    __internal_name__ = "JUMP"
    def __init__(self, destination):
        self.destination = destination

    def parse(self, raw_stmt):
        pass # todo 

    def __str__(self):
        return "JUMP {}".format(self.destination)

class TAC_Jumpi:
    __internal_name__ = "JUMPI"
    def __init__(self, condition, destination):
        self.condition = condition
        self.destination = destination

    def parse(self, raw_stmt):
        pass # todo 

    def __str__(self):
        return "JUMPI {} {}".format(self.condition, self.destination)

