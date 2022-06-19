import z3

from SEtaac.exceptions import SymbolicError
from SEtaac.utils import concrete, translate_xid


class SymbolicMemory(object):
    MAX_SYMBOLIC_WRITE_SIZE = 256

    def __init__(self):
        self.memory = z3.K(z3.BitVecSort(256), z3.BitVecVal(0, 8))
        self.write_count = 0
        self.read_count = 0

    def __getitem__(self, index):
        if isinstance(index, slice):
            if index.stop is None:
                raise ValueError("Need upper memory address!")
            if (index.start is not None and not concrete(index.start)) or not concrete(index.stop):
                raise SymbolicError("Use mem.read for symbolic range reads")
            r = []
            for i in range(index.start or 0, index.stop, index.step or 1):
                r.append(self[i])
            return r
        else:
            self.read_count += 1
            v = z3.simplify(self.memory[index])
            if z3.is_bv_value(v):
                return v.as_long()
            else:
                return v

    def __setitem__(self, index, v):
        if isinstance(index, slice):
            if index.stop is None:
                raise ValueError("Need upper memory address!")
            if (index.start is not None and not concrete(index.start)) or not concrete(index.stop):
                raise SymbolicError("Use mem.write for symbolic range writes")
            for j, i in enumerate(range(index.start or 0, index.stop, index.step or 1)):
                self[i] = v[j]
        else:
            self.write_count += 1
            if isinstance(v, str):
                v = ord(v)

            if concrete(v):
                old_v = self[index]
                if not concrete(old_v) or old_v != v:
                    self.memory = z3.Store(self.memory, index, v)
            else:
                self.memory = z3.Store(self.memory, index, v)

    def read(self, start, size):
        if concrete(start) and concrete(size):
            return self[start:start + size]
        elif concrete(size):
            return [self[start + i] for i in range(size)]
        else:
            sym_mem = SymbolicMemory()
            sym_mem.memory = self.memory
            return SymRead(sym_mem, start, size)
            # raise SymbolicError("Read of symbolic length")

    def copy_return_data(self, istart, ilen, ostart, olen):
        if concrete(ilen) and concrete(olen):
            self.write(ostart, olen, self.read(istart, min(ilen, olen)) + [0] * max(olen - ilen, 0))
        elif concrete(olen):
            self.write(ostart, olen, [z3.If(i < ilen, self[istart + i], 0) for i in range(olen)])
        else:
            self.write(ostart, SymbolicMemory.MAX_SYMBOLIC_WRITE_SIZE,
                       [z3.If(i < olen, z3.If(i < ilen, self[istart + i], 0), self[ostart + i]) for i in
                        range(SymbolicMemory.MAX_SYMBOLIC_WRITE_SIZE)])

    def copy(self, old_xid, new_xid):
        new_memory = SymbolicMemory()

        new_memory.memory = translate_xid(self.memory, old_xid, new_xid)
        new_memory.write_count = self.write_count
        new_memory.read_count = self.read_count

        return new_memory

    def write(self, start, size, val):
        if not concrete(size):
            raise SymbolicError("Write of symbolic length")
        if len(val) != size:
            raise ValueError("value does not match length")
        if concrete(start) and concrete(size):
            self[start:start + size] = val
        else:  # by now we know that size is concrete
            for i in range(size):
                self[start + i] = val[i]

    def set_enforcing(self, enforcing=True):
        pass

    def extend(self, start, size):
        pass


class SymRead(object):
    def __init__(self, memory, start, size):
        self.memory = memory
        self.start = start
        if not concrete(start):
            self.start = z3.simplify(self.start)
        self.size = size
        if not concrete(size):
            self.size = z3.simplify(self.size)

    def translate(self, old_xid, new_xid):
        sym_mem_mem = translate_xid(self.memory.memory, old_xid, new_xid)
        sym_mem = SymbolicMemory()
        sym_mem.memory = sym_mem_mem
        new_symread = SymRead(sym_mem, 0, 0)
        new_symread.start = self.start if concrete(self.start) else translate_xid(self.start, old_xid, new_xid)
        new_symread.size = self.size if concrete(self.size) else translate_xid(self.size, old_xid, new_xid)
        return new_symread
