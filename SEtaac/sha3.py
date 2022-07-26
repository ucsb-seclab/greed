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

        # The source memory where we are fetching data from
        self.memory = memory
        # Where to start to hash in the source memory
        self.start = start
        # How much we should hash 
        self.size = size

        # Let's start to copy at offset 0 of this lambda memory (it's _base) the amount 
        # of bytes 'size' starting from 'start'
        self.memcopy(BVV(0, 256), memory, start, size)

        # todo: we somehow want to make sure that there is never a constraint of the type SHA3_<x> == 0xhardcoded

    def instantiate_ackermann_constraints(self, other):
        assert isinstance(other, Sha3)

        # we need a unique common symbol to "scan" both arrays and then ensure that they cannot be different
        ackermann_index = BVS(f"ACKERMANN_INDEX_{self.ackermann_uuid_generator.next()}_SHA3_{self.uuid}", 256)

        sha_data_len_is_equal = Equal(self.size, other.size)

        # This is triggering reads over the lambda memory model. 
        # It instantiates the lambda constraints using as a reading offset the newly created Ackermann index.
        # 'sha_data_is_different_for_some_index' express the fact that the 2 memory region can be different for 
        # some accesses at the same index. Hence, this can be used to decide if the 2 sha symbols are 
        # the same or not later.
        sha_data_is_different_for_some_index = NotEqual(self[ackermann_index], other[ackermann_index])
        
        # This formula is used to detect if "it's not possible that the memory at which the SHA(s) are pointing 
        # have something difference for all the accesses at the same index". This means the SHA must be equal.
        sha_data_is_equal_for_all_indices = Not(sha_data_is_different_for_some_index)

        # Here we are building the final formulat that summarizes the comparison between the two SHA(s)
        # being compared.
        #return [If(And(sha_data_len_is_equal, sha_data_is_equal_for_all_indices),
        #           Equal(self.symbol, other.symbol),
        #           NotEqual(self.symbol, other.symbol)),
        #        BV_ULT(ackermann_index, self.size)]

        return [If(Equal(self.symbol, other.symbol), 
                        And(sha_data_is_equal_for_all_indices, sha_data_len_is_equal), 
                        Or(sha_data_is_different_for_some_index, 
                           NotEqual(self.size, other.size))),
                   BV_ULT(ackermann_index, self.size)]