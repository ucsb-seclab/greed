from SEtaac.utils.extra import UUIDGenerator
from SEtaac.utils.solver.shortcuts import *


class LambdaConstraint:
    def instantiate(self, index):
        return []


class LambdaMemsetConstraint(LambdaConstraint):
    def __init__(self, array, start, value, size, new_array, parent):
        self.array = array
        self.start = start
        self.value = value
        self.size = size

        self.new_array = new_array
        self.parent = parent

    def instantiate(self, index):
        index_in_range = BV_And(BV_ULE(self.start, index), BV_ULT(index, BV_Add(self.start, self.size)))
        instance = Equal(Array_Select(self.new_array, index),
                         If(index_in_range,
                            self.value,
                            Array_Select(self.array, index)))

        return [instance] + self.parent.instantiate(index)


class LambdaMemsetInfiniteConstraint(LambdaConstraint):
    def __init__(self, array, start, value, new_array, parent):
        self.array = array
        self.start = start
        self.value = value

        self.new_array = new_array
        self.parent = parent

    def instantiate(self, index):
        index_in_range = BV_ULE(self.start, index)
        instance = Equal(Array_Select(self.new_array, index),
                         If(index_in_range,
                            self.value,
                            Array_Select(self.array, index)))

        return [instance] + self.parent.instantiate(index)


class LambdaMemcopyConstraint(LambdaConstraint):
    def __init__(self, array, start, source, source_start, size, new_array, parent):
        self.array = array
        self.start = start
        self.source = source
        self.source_start = source_start
        self.size = size

        self.new_array = new_array
        self.parent = parent

    def instantiate(self, index):
        index_in_range = BV_And(BV_ULE(self.start, index), BV_ULT(index, BV_Add(self.start, self.size)))
        shift_to_source_offset = BV_Sub(self.source_start, self.start)
        instance = Equal(Array_Select(self.new_array, index),
                         If(index_in_range,
                            # memcopy source is of type "memory", don't access directly as an array
                            self.source[BV_Add(index, shift_to_source_offset)],
                            Array_Select(self.array, index)))

        return [instance] + self.parent.instantiate(index)


class LambdaMemcopyInfiniteConstraint(LambdaConstraint):
    def __init__(self, array, start, source, source_start, new_array, parent):
        self.array = array
        self.start = start
        self.source = source
        self.source_start = source_start

        self.new_array = new_array
        self.parent = parent

    def instantiate(self, index):
        index_in_range = BV_ULE(self.start, index)
        shift_to_source_offset = BV_Sub(self.source_start, self.start)
        instance = Equal(Array_Select(self.new_array, index),
                         If(index_in_range,
                            # memcopy source is of type "memory", don't access directly as an array
                            self.source[BV_Add(index, shift_to_source_offset)],
                            Array_Select(self.array, index)))

        return [instance] + self.parent.instantiate(index)


class LambdaMemory:
    uuid_generator = UUIDGenerator()

    def __init__(self, tag=None, value_sort=None, default=None, partial_init=False):
        if partial_init:
            return
        assert tag is not None and value_sort is not None, "Invalid LambdaMemory initialization"

        self.tag = tag
        self.value_sort = value_sort
        self._base = Array(f"{self.tag}_{LambdaMemory.uuid_generator.next()}", BVSort(256), value_sort)

        self.lambda_constraint = LambdaConstraint()
        self.constraints = list()

        if default is not None:
            # use memsetinfinite to make this a ConstArray with default BVV(0, 8)
            self.memsetinfinite(BVV(0, 256), default)

        self.write_count = 0
        self.read_count = 0

    def __getitem__(self, index):
        assert not isinstance(index, slice), "slice memory read not implemented"

        self.read_count += 1

        # instantiate and add lambda constraints
        self.constraints += self.lambda_constraint.instantiate(index)

        return Array_Select(self._base, index)

    def __setitem__(self, index, v):
        self.write_count += 1

        self._base = Array_Store(self._base, index, v)

    def readn(self, index, n):
        assert is_concrete(n), "readn with symbolic length not implemented"
        assert bv_unsigned_value(n) != 0, "invalid readn with length=0"

        if bv_unsigned_value(n) == 1:
            return self[index]
        else:
            vv = list()
            for i in range(bv_unsigned_value(n)):
                vv.append(self[BV_Add(index, BVV(i, 256))])
            return BV_Concat(vv)

    def memset(self, start, value, size):
        old_base = self._base
        self._base = Array(f"{self.tag}_{LambdaMemory.uuid_generator.next()}", BVSort(256), BVSort(8))

        self.lambda_constraint = LambdaMemsetConstraint(old_base, start, value, size, self._base,
                                                        parent=self.lambda_constraint)

    def memsetinfinite(self, start, value):
        old_base = self._base
        self._base = Array(f"{self.tag}_{LambdaMemory.uuid_generator.next()}", BVSort(256), BVSort(8))

        self.lambda_constraint = LambdaMemsetInfiniteConstraint(old_base, start, value, self._base,
                                                                parent=self.lambda_constraint)

    def memcopy(self, start, source, source_start, size):
        old_base = self._base
        self._base = Array(f"{self.tag}_{LambdaMemory.uuid_generator.next()}", BVSort(256), BVSort(8))

        self.lambda_constraint = LambdaMemcopyConstraint(old_base, start, source, source_start, size, self._base,
                                                         parent=self.lambda_constraint)

    def memcopyinfinite(self, start, source, source_start):
        old_base = self._base
        self._base = Array(f"{self.tag}_{LambdaMemory.uuid_generator.next()}", BVSort(256), BVSort(8))

        self.lambda_constraint = LambdaMemcopyInfiniteConstraint(old_base, start, source, source_start, self._base,
                                                                 parent=self.lambda_constraint)

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
        new_memory = LambdaMemory(partial_init=True)
        new_memory.tag = self.tag
        new_memory._base = self._base
        new_memory.lambda_constraint = self.lambda_constraint
        new_memory.constraints = list(self.constraints)
        new_memory.write_count = self.write_count
        new_memory.read_count = self.read_count
        return new_memory
