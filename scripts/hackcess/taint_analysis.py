
import random
import logging 

from SEtaac.utils.solver.shortcuts import *
from SEtaac.memory.lambda_memory import LambdaMemcopyConstraint, LambdaMemsetInfiniteConstraint
from SEtaac.memory.utils import get_array_base

LOGGING_FORMAT = "%(levelname)s | %(name)s | %(message)s"
logging.basicConfig(level=logging.INFO, format=LOGGING_FORMAT)
log = logging.getLogger("taint_analysis")
log.setLevel(logging.INFO)


class CalldataTaintAnalysis:
    def __init__(self, state, taint_begins:int, taint_size:int):
        self.state = state
        self.taint_begins = taint_begins
        self.taint_size = taint_size

        self.extra_constraints = []

        self.curr_mem_read_index = None

    def is_mem_read_tainted(self, mem_read_index:int):
        self._is_mem_read_tainted(self.state.memory.lambda_constraint, mem_read_index)


    def _is_mem_read_tainted(self, lambda_layer, mem_read_index:int):
        self._inspect_lambda_layer(lambda_layer, mem_read_index)

    # This code is Yices specific...
    def _parse_val(self, lambda_layer, mem_read_index, data):
        if hasattr(data, "children"):
            children = data.children
            if data.operator == "bv-extract":
                self._parse_val(children[2])
            elif data.operator == "bvshr":
                self._parse_val(children[0])
            elif data.operator == "bv-concat":
                # Assuming that concat always operates over SELECTs,
                # (this maybe need to be fixed in the future)
                # We want to see if at least ONE of the SELECT is reading 
                # tainted data, if yes, we declare the original data tainted.
                for select in data.children:
                    if select.children[1].value == mem_read_index:
                        # Re-using a tainted value automatically taint the 
                        # data stored by the STORE. 
                        # As we found at least one byte of tainted data, we are done.
                        # FIXME: signal "data" is tainted
                        return True
                for select in data.children:
                    self._is_mem_read_tainted(lambda_layer, select.children[1].value)
            else:
                assert(False)

    def _get_array_base(self, array):
        if hasattr(array, "children"):
            for c in array.children:
                if hasattr(c, "operator"):
                    if c.operator == "store":
                        return self._get_array_base(c)
                    elif c.operator == "array":
                        return c.name

    def _inspect_lambda_layer(self, lambda_layer, mem_read_index:int):
        #print(f"Current lambda layer {type(lambda_layer)}")
        # First, let's check if there is ANY store (i.e., following_writes) in this lambda layer
        # that is masking the read at this offset.
        for fw in lambda_layer.following_writes:
            # SATCHECK
            if self.state.solver.is_formula_sat(Equal(fw, BVV(mem_read_index, 256))):
                log.info(f"{fw} is possibly writing at {mem_read_index}")
                # Ok, this store is writing over the read of interest.
                # Here we need to re-construct the dependecies of this value.
                # Now, we have to understand if the value that was stored was tainted or not.
                # If yes, this is still a valid tainted read, otherwise, this read offset was 
                # overwritten by a new value (in the latter case, we need to understand where is 
                # this value coming from).
                stored_data = lambda_layer.following_writes[fw]
                self._parse_val(lambda_layer, mem_read_index, stored_data)
                break
        else:
            # None of the store that have been issued at this layer can overwrite 
            # the read index. We can inspect directly the lambda layer itself.
            if isinstance(lambda_layer, LambdaMemsetInfiniteConstraint):
                # Is the mem_read_index falling withing the boundaries of the memset, if yes, this is trivially not tainted.
                read_in_memset_range =  BV_ULE(lambda_layer.start, BVV(mem_read_index, 256))

                # SATCHECK
                if self.state.solver.is_formula_true(read_in_memset_range):
                    # This read is definitely NOT tainted.
                    # (there are no solutions for which this falls out of the memset range)
                    return False
                else:
                    # This read can fall out of the memset, let's enforce that through constraints
                    # and go to the next layer! :D
                    new_constraint = Not(read_in_memset_range)
                    # Let's record it 
                    self.extra_constraints.append(new_constraint)
                    # And add it to the state
                    self.state.add_constraint(new_constraint)
                    # Go to next layer
                    self._inspect_lambda_layer(lambda_layer.parent, mem_read_index)

            if isinstance(lambda_layer, LambdaMemcopyConstraint):
                array_base_name = self._get_array_base(lambda_layer.source._base)
                import ipdb; ipdb.set_trace()
                
                # Check if we are copying from CALLDATA
                if "CALLDATA" in array_base_name:

                    # This calculates the shift of the memory<->CALLDATA copy.
                    delta_range = If( BV_UGE(lambda_layer.source_start, lambda_layer.start),
                                        BV_Sub(lambda_layer.source_start, lambda_layer.start),
                                        BV_Sub(lambda_layer.start, lambda_layer.source_start))

                    # Now we scan the boundaries of the tainted range
                    for taint_offset in range(self.taint_begins, self.taint_begins+self.taint_size):
                        # Is this taint_offset within the boundaries of the copy?
                        taint_offset_in_range = And(BV_ULE(lambda_layer.source_start, BVV(taint_offset,256)), 
                                                    BV_ULT(BVV(taint_offset,256), BV_Add(lambda_layer.source_start, 
                                                                                            lambda_layer.size)))
                        # SATCHECK
                        if self.state.solver.is_formula_sat(taint_offset_in_range):
                            # Ok, this taint_offset is within the boundaries specified by this copy 

                            # Calculating where this offset map in the destination memory
                            maps_to_memory_at = If(BV_UGE(lambda_layer.source_start, 
                                                            lambda_layer.start),
                                                    BV_Sub(BVV(taint_offset,256), delta_range),
                                                    BV_Add(BVV(taint_offset,256), delta_range))
                            # SATCHECK
                            if self.state.solver.is_formula_sat(Equal(BVV(mem_read_index,256), maps_to_memory_at)):
                                # Yup, this is tainted!
                                print(f"Read in memory at {mem_read_index} is tainted!")
                                import ipdb; ipdb.set_trace()
                                return True
                        else:
                            #print(f"Taint offset {taint_offset} not in scope of the current CALLDATACOPY. Skipping it.")
                            # This taint_offset is not falling within the region 
                            # copied from CALLDATA in this memcpy, skip it.
                            continue                        
                    # If we are here, we didn't find any matching taint at this level, let's walk 
                    # back the lambda chain and do the same thing.
                    self._inspect_lambda_layer(lambda_layer.parent, mem_read_index)
                else:
                    assert(False)
                    pass