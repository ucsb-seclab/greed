
import random
import logging 

from SEtaac.utils.solver.shortcuts import *
from SEtaac.memory.lambda_memory import LambdaMemcopyConstraint

from Enum import enum

LOGGING_FORMAT = "%(levelname)s | %(name)s | %(message)s"
logging.basicConfig(level=logging.INFO, format=LOGGING_FORMAT)
log = logging.getLogger("taint_analysis")
log.setLevel(logging.INFO)

class SourceTaint(Enum):
    CALLDATA = "CALLDATA"

# This code is Yices specific...
def parse_val(data):
    if hasattr(data, "children"):
        children = data.children
        
        # Here we basically want to implement the 
        # condition we want to check to see if data 
        # is tainted itself or not.
        if children.operator == "bv-extract":
            parse_val(children[2])
        elif children.operator == "bvshr":
            parse_val(children[0])
        else:
            assert(False)


def is_mem_read_tainted(state, source_name:SourceTaint, source_taint_start:int, source_taint_size:int, read_index_val:int):
    if source_name = SourceTaint.CALLDATA:
        # First, let's check if there is ANY store (i.e., following_writes) in the last lambda chain object 
        # that is masking the read at this offset.
        for fw in state.memory.lambda_constraint.following_writes:
            if found.solver.is_formula_sat(Equal(fw, BVV(read_index_val, 256))):
                log.info(f"{fw} is possibly writing at {read_index_val}")
                # Ok, this store is writing over the read of interest.
                # Here we need to re-construct the dependecies of this value.
                # Now, we have to understand if the value that was stored was tainted or not.
                # If yes, this is still a valid tainted read, otherwise, this read offset was 
                # overwritten by a new value (in the latter case, we need to understand where is 
                # this value coming from).
                stored_data = state.memory.lambda_constraint.following_writes[fw]
                parse_val(stored_data)
            else:
                # None of the store that have been issued at this layer can overwrite 
                # the read index, hence, we can directly check if this read_index come from
                # a specific lambda object.
                # Since we are looking for CALLDATA here, we are looking specifically 
                # for a memcpy object.
                if isinstance(state.memory.lambda_constraint, LambdaMemcopyConstraint):
                    # TODO make sure this is a copy from CALLDATA

                    # This calculates the shift of the memory<->CALLDATA copy.
                    delta_range = If( BV_UGE(found.memory.lambda_constraint.source_start, found.memory.lambda_constraint.start),
                                        BV_Sub(found.memory.lambda_constraint.source_start, found.memory.lambda_constraint.start),
                                        BV_Sub(found.memory.lambda_constraint.start, found.memory.lambda_constraint.source_start))
                
                    for x in range(source_taint_start, source_taint_start+source_taint_size):
                        x_bvv = BVV(x,256)
                        maps_to_memory_at = If(BV_UGE(found.memory.lambda_constraint.source_start, 
                                                        found.memory.lambda_constraint.start),
                                                BV_Sub(x_bvv, delta_range),
                                                BV_Add(x_bvv, delta_range))
                        if state.solver.is_sat(Equal(BVV(read_index_val), maps_to_memory_at)):
                            # Ok, our read_index_val maps inside the taint specified at the beginning! 
                            pass
                    else:
                        # Ok, no mapping withing the tainted range, is there another layer we need to check?
                        # Basically here we need to repeat the same story but for the parent layer.
    else:
        assert(False)