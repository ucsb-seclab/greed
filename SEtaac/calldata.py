from SEtaac.utils.solver.shortcuts import *


class SymbolicCalldata(object):
    def __init__(self, xid, default=None, partial_init=False):
        self.xid = xid
        if partial_init:
            return

        if default is not None:
            self.base = ConstArray(f"CALLDATA_{self.xid}", BVSort(256), BVSort(8), default)
        else:
            self.base = Array(f"CALLDATA_{self.xid}", BVSort(256), BVSort(8))

    def __getitem__(self, index):
        if isinstance(index, slice):
            raise Exception("slice read on CALLDATA not implemented")
        else:
            v = Array_Select(self.base, index)
            return v

    def __setitem__(self, index, v):
        self.base = Array_Store(self.base, index, v)

    def readn(self, index, n):
        if not is_concrete(n):
            # As of now we are not using it (should never be called),
            # hence, we are not implementing it.
            raise Exception("readn with symbolic length not implemented")
        elif bv_unsigned_value(n) == 1:
            return self[index]
        else:
            vv = list()
            for i in range(bv_unsigned_value(n)):
                vv.append(self[BV_Add(index, BVV(i, 256))])
            return BV_Concat(vv)

    def copy(self):
        new_calldata = SymbolicCalldata(xid=self.xid, partial_init=True)
        new_calldata.base = self.base
        return new_calldata
