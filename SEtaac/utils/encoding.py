TT256 = 2 ** 256
TT256M1 = 2 ** 256 - 1
TT255 = 2 ** 255
SECP256K1P = 2 ** 256 - 4294968273


def addr(expr):
    return expr & (2 ** 160 - 1)


def big_endian_to_int(x):
    return int.from_bytes(x, byteorder='big')


def int_to_big_endian(v):
    return v.to_bytes(length=(v.bit_length() + 7) // 8, byteorder='big')


def bytearray_to_bytestr(value):
    return bytes(value)


def encode_int32(v):
    return int_to_big_endian(v).rjust(32, b'\x00')


def bytes_to_int(value):
    return big_endian_to_int(bytes(value))


def to_signed(i):
    return i if i < TT255 else i - TT256
