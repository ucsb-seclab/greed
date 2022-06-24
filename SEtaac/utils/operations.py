import numbers
from sha3 import keccak_256


def sha3(data):
    return keccak_256(data).digest()


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
