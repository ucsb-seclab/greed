from SEtaac.memory import LambdaMemory
from SEtaac.utils.extra import UUIDGenerator
from SEtaac.utils.solver.shortcuts import *
from SEtaac import options


class Sha3(LambdaMemory):
    """
    SHA3 needs to be of type LambdaMemory to allow the (bounded) comparison between two SHA(s) (see ca. line 50).
    """
    uuid_generator = UUIDGenerator()

    def __init__(self, state=None, memory=None, start=None, size=None, partial_init=False):

        if partial_init:
            return 

        self.uuid = Sha3.uuid_generator.next()

        super().__init__(tag=f"SHA3_{self.uuid}_MEMORY", value_sort=BVSort(8), default=BVV(0, 8), state=state)
        self.symbol = BVS(f"SHA3_{self.uuid}", 256)

        self.state = state
        
        # The source memory where we are fetching data from
        self.memory = memory.copy(self.state)
        # Where to start to hash in the source memory
        self.start = start
        # How much we should hash 
        self.size = size

        # limit max size to max_size
        self.max_size = options.MAX_SHA_SIZE
        self.add_constraint(BV_ULE(self.size, BVV(self.max_size, 256)))

        # Let's start to copy at offset 0 of this lambda memory (it's _base) the amount 
        # of bytes 'size' starting from 'start'
        self.memcopy(BVV(0, 256), self.memory, start, size)

        # TODO: we somehow want to make sure that there is never a constraint of the type SHA3_<x> == 0xhardcoded

    def instantiate_ackermann_constraints(self, other):
        assert isinstance(other, Sha3)

        sha_data_len_is_equal = Equal(self.size, other.size)

        # Here we are building the final formula that summarizes the (bounded) comparison between the two SHA(s)
        # This instantiates the lambda constraints using as a reading offsets all the indexes in the range (0, max_size)
        bounded_bytes_are_equal = list()
        for i in range(self.max_size):
            bounded_bytes_are_equal.append(Equal(self[BVV(i, 256)], other[BVV(i, 256)]))

        sha_equal = Equal(self.symbol, other.symbol)
        sha_not_equal = NotEqual(self.symbol, other.symbol)

        sha_distance = If(BV_UGE(self.symbol, other.symbol), 
                                BV_Sub(self.symbol, other.symbol),
                                BV_Sub(other.symbol, self.symbol))

        sha_distance_more_than_x = BV_SGT(sha_distance, BVV(options.MIN_SHA_DISTANCE, 256))

        bounded_ackermann_constraint = If(And(*([sha_data_len_is_equal] + bounded_bytes_are_equal)),
                                          sha_equal,
                                          And(sha_not_equal, sha_distance_more_than_x))

        self.add_constraint(bounded_ackermann_constraint)
    
    def copy(self, new_state):
        new_sha_memory = Sha3(partial_init=True)
        new_sha_memory.uuid = self.uuid
        new_sha_memory.tag = self.tag
        new_sha_memory._base = self._base
        new_sha_memory.lambda_constraint = self.lambda_constraint
        new_sha_memory._constraints = list(self._constraints)
        new_sha_memory.write_count = self.write_count
        new_sha_memory.read_count = self.read_count
        new_sha_memory.layer_level = self.layer_level
        new_sha_memory.symbol = self.symbol

        # WARNING: does this need a deep copy?
        new_sha_memory.memory = self.memory

        new_sha_memory.start = self.start
        new_sha_memory.size = self.size
        new_sha_memory.max_size = self.max_size
        
        return new_sha_memory
