class BB(object):
    def __init__(self, ins):
        self.ins = ins

        self.start = self.ins[0].addr

        self.branch = self.ins[-1].op == 0x57
        self.indirect_jump = self.ins[-1].op in (0x56, 0x57)
