from SEtaac.lambda_memory import LambdaMemory
from SEtaac.utils.extra import UUIDGenerator
from SEtaac.utils.solver.shortcuts import *


class Sha3(LambdaMemory):
    uuid_generator = UUIDGenerator()

    def __init__(self, memory, start, size):
        self.uuid = Sha3.uuid_generator.next()
        self.ackermann_uuid_generator = UUIDGenerator()
        super().__init__(tag=f"SHA3_{self.uuid}_MEMORY", value_sort=BVSort(8), default=BVV(0, 8))
        self.symbol = BVS(f"SHA3_{self.uuid}", 256)

        self.memory = memory
        self.start = start
        self.size = size

        self.memcopy(BVV(0, 256), memory, start, size)

        # todo: we somehow want to make sure that there is never a constraint of the type SHA3_<x> == 0xhardcoded

    def instantiate_ackermann_constraints(self, other):
        assert isinstance(other, Sha3)

        # we need a unique common symbol to "scan" both arrays and then ensure that they cannot be different
        ackermann_index = BVS(f"ACKERMANN_INDEX_{self.ackermann_uuid_generator.next()}_SHA3_{self.uuid}", 256)

        sha_data_len_is_equal = Equal(self.size, other.size)
        sha_data_is_different_for_some_index = NotEqual(self[ackermann_index], other[ackermann_index])
        sha_data_is_equal_for_all_indices = Not(sha_data_is_different_for_some_index)

        return [If(And(sha_data_len_is_equal, sha_data_is_equal_for_all_indices),
                   Equal(self.symbol, other.symbol),
                   NotEqual(self.symbol, other.symbol)),
                BV_ULT(ackermann_index, self.size)]


