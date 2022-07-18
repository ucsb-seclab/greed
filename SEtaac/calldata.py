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
            if is_concrete(index.start) and is_concrete(index.stop):
                vv = list()
                for i in range(bv_unsigned_value(index.stop) - bv_unsigned_value(index.start)):
                    vv.append(Array_Select(self.base, BV_Add(index.start, BVV(i, 256))))
                return BV_Concat(vv)
            else:
                raise Exception("Symbolic read on CALLDATA not implemented")
        else:
            v = Array_Select(self.base, index)
            return v

    def __setitem__(self, index, v):
        self.base = Array_Store(self.base, index, v)

    def copy(self):
        new_calldata = SymbolicCalldata(xid=self.xid, partial_init=True)
        new_calldata.base = self.base
        return new_calldata
