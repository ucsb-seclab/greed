
import logging
import web3
import sys 

from SEtaac import options as opt
from SEtaac.memory.lambda_constraint import LambdaConstraint
from SEtaac.memory import LambdaMemory
from SEtaac.utils.exceptions import GreedException
from SEtaac.solver.shortcuts import *
from SEtaac.utils.extra import UUIDGenerator

log = logging.getLogger(__name__)
log.setLevel(logging.INFO)

def get_storage(contract_address, index):
    """
    (cached for performance)
    Retrieve storage value from the blockchain
    """
    
class PartialConcreteStorage:

    uuid_generator = UUIDGenerator()

    def __init__(self, tag=None, value_sort=None, default=None, state=None, partial_init=False):
        if partial_init:
            return
        assert tag is not None and value_sort is not None, "Invalid PartialConcreteStorage initialization"

        self.tag = tag
        self.value_sort = value_sort

        self.state = state
        
        if "ADDRESS" not in self.state.ctx:
            raise GreedException("Cannot initialize the PartialConcreteStorage with no contract address")
        else:
            self.contract_address = self.state.ctx["ADDRESS"]

        if "NUMBER" not in self.state.ctx:
            raise GreedException("Cannot initialize the PartialConcreteStorage with no reference block")
        else:
            self.chain_at = self.state.ctx["NUMBER"]
        
        # Configure web3py
        # The connection string can be put in a config file.
        self.w3 = web3.Web3(web3.Web3.HTTPProvider(opt.WEB3_PROVIDER))
        assert(self.w3.isConnected())
        
        self.root_lambda_constraint = LambdaConstraint()
        self._constraints = list()
        
        self._base = Array(f"{self.tag}_{PartialConcreteStorage.uuid_generator.next()}_{self.layer_level}", BVSort(256), value_sort)
        if default is not None:
            # use memsetinfinite to make this a ConstArray with default BVV(0, 8)
            self.memsetinfinite(BVV(0, 256), default)

        self.write_count = 0
        self.read_count = 0
        
        self.concrete_cache = dict()
    
    def add_constraint(self, formula):
        self.state.solver.add_memory_constraints(formula)

    def add_constraints(self, formulas):
        for formula in formulas:
            self.add_constraint(formula)

    @property
    def layer_level(self):
        return self.root_lambda_constraint.depth - 1

    @property
    def constraints(self):
        return self._constraints

    def __getitem__(self, index):
        assert not isinstance(index, slice), "slice memory read not implemented"

        self.read_count += 1
        
        if is_concrete(index):
            # Grab the concrete value
            index_val = index.value
            
            if index_val not in self.concrete_cache.keys():
                log.info(f"Concrete read from chain@{self.chain_at} for storage index [{hex(index_val)}]")
                storage_value = self.w3.eth.getStorageAt(self.contract_address, index_val,  block_identifier=self.chain_at)
                log.info(f"   Value read is: {storage_value.hex()}")
                storage_value = int(storage_value.hex(),16)
                storage_value_bvv = BVV(storage_value, 256)
                return storage_value_bvv
            else:
                log.debug(f"Concrete read from concrete cache")
                return self.concrete_cache[index_val]
        
        # TODO: also check if we have one possible solution and concretize it?
        
        # instantiate and add lambda constraints
        new_constraints = self.root_lambda_constraint.instantiate(index)
        self.add_constraints(new_constraints)

        return Array_Select(self._base, index)

    def __setitem__(self, index, v):
        self.write_count += 1

        if is_concrete(index):
            # Grab the concrete value
            index_val = index.value
            self.concrete_cache[index_val] = v
        else:
            # It should be ok?
            self.root_lambda_constraint.following_writes[index] = v
            self._base = Array_Store(self._base, index, v)

    def readn(self, index, n):
        assert is_concrete(n), "readn with symbolic length not implemented"
        assert bv_unsigned_value(n) != 0, "invalid readn with length=0"
        if bv_unsigned_value(n) == 1:
            return self[index]
        else:
            vv = list()
            for i in range(bv_unsigned_value(n)):
                read_index = BV_Add(index, BVV(i, 256))
                vv.append(self[read_index])
            return BV_Concat(vv)

    def memset(self, start, value, size):
        old_base = self._base
        self._base = Array(f"{self.tag}_{PartialConcreteStorage.uuid_generator.next()}_{self.layer_level}", BVSort(256), BVSort(8))

        self.root_lambda_constraint = LambdaMemsetConstraint(old_base, start, value, size, self._base,
                                                             parent=self.root_lambda_constraint)

    def memsetinfinite(self, start, value):
        old_base = self._base
        self._base = Array(f"{self.tag}_{PartialConcreteStorage.uuid_generator.next()}_{self.layer_level}", BVSort(256), BVSort(8))

        self.root_lambda_constraint = LambdaMemsetInfiniteConstraint(old_base, start, value, self._base,
                                                                     parent=self.root_lambda_constraint)

    def memcopy(self, start, source, source_start, size):
        old_base = self._base
        self._base = Array(f"{self.tag}_{PartialConcreteStorage.uuid_generator.next()}_{self.layer_level}", BVSort(256), BVSort(8))

        self.root_lambda_constraint = LambdaMemcopyConstraint(old_base, start, source, source_start, size, self._base,
                                                              parent=self.root_lambda_constraint)

    def memcopyinfinite(self, start, source, source_start):
        old_base = self._base
        self._base = Array(f"{self.tag}_{PartialConcreteStorage.uuid_generator.next()}_{self.layer_level}", BVSort(256), BVSort(8))

        self.root_lambda_constraint = LambdaMemcopyInfiniteConstraint(old_base, start, source, source_start, self._base,
                                                                      parent=self.root_lambda_constraint)

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

    def copy(self, new_state):
        new_memory = PartialConcreteStorage(partial_init=True)
        new_memory.tag = self.tag
        new_memory._base = self._base
        new_memory.state = new_state
        new_memory.root_lambda_constraint = self.root_lambda_constraint.copy(new_state=new_state)
        new_memory._constraints = list(self._constraints)
        new_memory.write_count = self.write_count
        new_memory.read_count = self.read_count
        
        # Specific attributes
        new_memory.w3 = self.w3
        new_memory.chain_at = self.chain_at
        new_memory.contract_address = self.contract_address
        new_memory.concrete_cache = self.concrete_cache
        
        return new_memory

    def __str__(self):
        return f"PartialConcreteStorage\n" \
               f"{self.root_lambda_constraint}"
