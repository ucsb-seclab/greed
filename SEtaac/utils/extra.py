class UUIDGenerator(object):
    def __init__(self):
        self.value = 0

    def next(self):
        self.value += 1
        return self.value


XID_GENERATOR = UUIDGenerator()


def gen_exec_id():
    return XID_GENERATOR.next()
