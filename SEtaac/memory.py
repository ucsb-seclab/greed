from SEtaac.utils.solver.shortcuts import *


class SymbolicMemory(object):
    MAX_SYMBOLIC_WRITE_SIZE = 256

    def __init__(self, partial_init=False, tag='MEMORY'):
        if partial_init:
            return  

        self.lambda_index = BVS("LAMBDA_INDEX", 256)
        self.lambda_memory_read = BVV(0,8)

        self.write_count = 0
        self.read_count = 0

    def __getitem__(self, index):
        self.read_count += 1
        if isinstance(index, slice):
            raise Exception("slice read on MEMORY not implemented")
        else:
            v = Array_Select(self.memory, index)
            return v

    def __setitem__(self, index, v):
        self.write_count += 1
        self.memory = Array_Store(self.memory, index, v)

    def readn(self, index, n):
        if not is_concrete(n):
            return SymRead(self.memory, index, BV_Add(index, BVV(n, 256)))
        elif n == 1:
            return self[index]
        else:
            vv = list()
            for i in range(n):
                vv.append(self[BV_Add(index, BVV(i, 256))])
            return BV_Concat(vv)

    def copy_return_data(self, istart, ilen, ostart, olen):
        raise Exception("NOT IMPLEMENTED. Please have a look")
        # if concrete(ilen) and concrete(olen):
        #     self.write(ostart, olen, self.read(istart, min(ilen, olen)) + [0] * max(olen - ilen, 0))
        # elif concrete(olen):
        #     self.write(ostart, olen, [z3.If(i < ilen, self[istart + i], 0) for i in range(olen)])
        # else:
        #     self.write(ostart, SymbolicMemory.MAX_SYMBOLIC_WRITE_SIZE,
        #                [z3.If(i < olen, z3.If(i < ilen, self[istart + i], 0), self[ostart + i]) for i in
        #                 range(SymbolicMemory.MAX_SYMBOLIC_WRITE_SIZE)])

    def copy(self, old_xid, new_xid):
        if old_xid != new_xid:
            raise Exception("memory copy with different xid is not implemented. Please have a look")
        new_memory = SymbolicMemory(partial_init=True)
        new_memory.memory = self.memory
        new_memory.write_count = self.write_count
        new_memory.read_count = self.read_count
        return new_memory


# Represents a full symbolic read over memory
class SymRead:
    def __init__(self, memory, start, end):
        self.memory = memory
        self.start = start
        self.end = end
        self.size = BV_Add(BV_Sub(self.end, self.start), BVV(1, 256))
