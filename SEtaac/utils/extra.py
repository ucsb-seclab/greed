class UUIDGenerator(object):
    def __init__(self):
        self.value = 0

    def next(self):
        self.value += 1
        return self.value


XID_GENERATOR = UUIDGenerator()


def gen_exec_id():
    return XID_GENERATOR.next()


def is_pow2(x):
    return x and not x & (x - 1)


def log2(x):
    if not is_pow2(x):
        raise ValueError("%d is not a power of 2!" % x)
    i = -1
    while x:
        x >>= 1
        i += 1
    return i