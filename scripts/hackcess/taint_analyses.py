import logging

from SEtaac.solver.shortcuts import *
from sha_resolver import ShaResolver
from utils import bcolors


# source_start: this is an offset in CALLDATA 
# source_end: this is an offset in CALLDATA
#     source_start + source_end define a range considered 
#     as the source of this taint analysis.
#     (DEFAULT: all CALLDATA but the 4 first bytes

# "state" is the current state at the CALL considered for the analysis.

# NOTE: Maker sure source_start <-> source_end was declared as symbolic, otherwise
#       the solutions are fixed since the beginning. 
#       If this will become an official API, we need to build a more friendly plugin.
class CalldataToFuncTarget():
    def __init__(self, state, source_start=4, source_end=-1, sha_deps=None):
        
        self.state = state
        
        assert(self.state.curr_stmt.__internal_name__ == "CALL")

        self.log = logging.getLogger("taint_analysis")
        self.log.setLevel(logging.INFO)

        self.starting_frame = self.state.solver.frame

        # Source parameters
        self.source_start = source_start

        if source_end == -1:
            source_end = self.state.MAX_CALLDATA_SIZE - 1

        self.source_end = source_end
        self.source_size = self.source_end - self.source_start

        # Convert to solver types
        self.source_start = BVV(self.source_start, 256)
        self.source_end   = BVV(self.source_end, 256)
        self.source_size  = BVV(self.source_size, 256)

        assert(is_concrete(self.source_start) and is_concrete(self.source_end))

        # Check if the bytes marked as tainted are symbolic or not.
        # If they are initialized concretely, we considerably limit the 
        # amount of solution we can get later. This can impact the
        # taint analysis if not used carefully.
        tainted_concrete_guard = False
        for index in range(source_start, source_end+1):
            if is_concrete(self.state.calldata[BVV(index,256)]):
                tainted_concrete_guard = True
        if tainted_concrete_guard:
            self.log.warning(f"Some CALLDATA bytes tainted, but initialized with concrete data.")
        
        # Get an instance for the sha resolver
        
        self.sha_resolver = ShaResolver(self.state, sha_deps=sha_deps)
        self.sha_resolver.detect_sha_dependencies()
        
        self.state_has_shas = True if len(self.sha_resolver.sha_deps) != 0 else False

        self.log.debug(f"Taint applied to CALLDATA[{self.source_start}:{self.source_end}] (size: {self.source_size})")

        self.is_tainted = False

    def to_human(self, val, size):
        return bv_unsigned_value(val).to_bytes(bv_unsigned_value(size), 'big').hex()
    
    def run(self):
        
        assert(self.state.solver.frame==0)

        self.log.info("Starting CALLDATA to funcTarget taint analysis")

        calldata_sol = self.state.solver.eval_memory_at(self.state.calldata, self.source_start, self.source_size, raw=True)

        self.log.info(f"Using CALLDATA[{self.source_start.value}:{self.source_end.value}] {self.to_human(calldata_sol, self.source_size)}")

        whole_calldata = self.state.solver.eval_memory(self.state.calldata, BVV(self.state.MAX_CALLDATA_SIZE,256), raw=True)
        self.log.debug(f"{self.to_human(whole_calldata, BVV(self.state.MAX_CALLDATA_SIZE,256))}")

        # Fix this solution in a new frame (+1)
        self.state.solver.push()
        self.state.add_constraint(Equal(calldata_sol, self.state.calldata.readn(self.source_start, self.source_size)))

        # Resolve SHAs if any (this also fix the solutions in the solver in a new frame) (+1)
        if self.state_has_shas:
            self.sha_resolver.fix_shas()
        else:
            assert(self.state.solver.frame == 1)

        # Get solution for CALL parameters
        mem_offset_call_raw = self.state.solver.eval(self.state.registers[self.state.curr_stmt.arg4_var], raw=True)
        mem_offset_call = bv_unsigned_value(mem_offset_call_raw)
        self.log.info(f"Using {mem_offset_call} as argOffset for CALL state")
        
        # Here we consider only the first 4 bytes
        mem_argSize = mem_offset_call + 4 - mem_offset_call
        mem_argSize_raw = BVV(mem_argSize, 256)

        # Maybe make sure the argSize is at least greater than 4 for every possible solution?
        #assert(self.state.solver.is_formula_true(BV_UGT(mem_argSize_raw, BVV(4,256))))

        self.log.info(f"Using {mem_argSize} as argSize for CALL state")

        # Fix the offset (+1)
        self.state.solver.push()
        self.state.add_constraint(Equal(mem_offset_call_raw, self.state.registers[self.state.curr_stmt.arg4_var]))

        mem_at_call_raw = self.state.solver.eval_memory_at(self.state.memory, mem_offset_call_raw, mem_argSize_raw, raw=True)
        mem_at_call = bv_unsigned_value(mem_at_call_raw)
        self.log.info(f"funcTarget at CALL is: 0x{self.to_human(mem_at_call_raw, mem_argSize_raw)}")

        # Now, we want to see what happen when we change CALLDATA and SHAs.

        # removes the mem_offset_call (-1)
        self.state.solver.pop()
        
        # removes sha constraints (-1)
        if self.state_has_shas:
            self.state.solver.pop()

        # remove calldata constraints (-1)
        self.state.solver.pop()


        # HERE FRAMEs ARE CLEAN (0)
        assert(self.state.solver.frame == 0 )

        # Add frame to avoid previous CALLDATA solution (+1)
        self.state.solver.push()
        # We don't want the previous one
        self.state.add_constraint(NotEqual(calldata_sol, self.state.calldata.readn(self.source_start, self.source_size)))
        # We want to re-use the same offset as before as of now
        self.state.add_constraint(Equal(mem_offset_call_raw, self.state.registers[self.state.curr_stmt.arg4_var]))

        # Get new solution for CALLDATA
        #new_calldata_sol = self.state.solver.eval_memory_at(self.state.calldata, self.source_start, self.source_size, raw=True)
        #self.state.add_constraint(Equal(new_calldata_sol, self.state.calldata.readn(self.source_start, self.source_size)))

        #self.log.info(f" Using CALLDATA[4:] {self.to_human(new_calldata_sol, self.source_size)}")
        #new_whole_calldata = self.state.solver.eval_memory(self.state.calldata, BVV(self.state.MAX_CALLDATA_SIZE,256), raw=True)
        #print(f"{self.to_human(new_whole_calldata, BVV(self.state.MAX_CALLDATA_SIZE,256))}")

        # Resolve SHAs if any (this also fix the solutions in the solver in a new frame)
        # We have to do this to avoid spurious solutions related to the fact that as of now
        # there is no correlation between SHAs input buffers and the symbolic variable representing the SHAs.

        # NOTE: This might impact the solutions for CALLDATA later.
        if self.state_has_shas:
            self.sha_resolver.clear_solutions()
            self.sha_resolver.fix_shas() # (+1)

        # If this is not SAT, we cannot reach the same state with a different CALLDATA!
        if not self.state.solver.is_sat():
            self.log.fatal("Cannot reach same state with a different CALLDATA!")
        else:
            # DISCUSSION: at this point, if the state is sat, it means that there exist CALLDATA values (different from the 
            # previous one) that respect the SHAs solutions we just set.
            
            # DISCUSSION: if the memory at CALL is ALWAYS equal to the mem calculated before ( i.e., a different CALLDATA cannot change
            # the outcome of the bytes at this location, then we conclude that the mem_at_call is not dependent from the CALLDATA bytes)
            if self.state.solver.is_formula_true(Equal(mem_at_call_raw, self.state.memory.readn(mem_offset_call_raw, BVV(4,256)))):
                self.log.info(f"{bcolors.BLUEBG}funcTarget at CALL does NOT depend from source!{bcolors.ENDC}")
            else:
                # DISCUSSION: in this case it means that there exist a possibility for a different CALLDATA to create a different 
                # mem_at_call, hence, we conclude this is tainted!
                self.log.info(f"{bcolors.REDBG}funcTarget at CALL depends from source!{bcolors.ENDC}")
                # Let's create a solution for that :) 
                self.state.add_constraint(NotEqual(mem_at_call_raw, self.state.memory.readn(mem_offset_call_raw, mem_argSize_raw)))
                new_calldata = self.state.solver.eval_memory(self.state.calldata, BVV(self.state.MAX_CALLDATA_SIZE,256), raw=True)
                new_memory_at_call = self.state.solver.eval_memory_at(self.state.memory, mem_offset_call_raw, mem_argSize_raw, raw=True)
                self.log.info(f"Possible solution:")
                self.log.info(f" CALLDATA: {self.to_human(new_calldata, BVV(self.state.MAX_CALLDATA_SIZE,256))}")
                self.log.info(f"funcTarget at CALL: 0x{self.to_human(new_memory_at_call, mem_argSize_raw)}")
                
                self.is_tainted = True
                

class CalldataToContractTarget():
    def __init__(self, state, source_start=4, source_end=-1, sha_deps=None):
        self.state = state
        
        assert(self.state.curr_stmt.__internal_name__ == "CALL")

        self.log = logging.getLogger("taint_analysis")
        self.log.setLevel(logging.INFO)

        self.starting_frame = self.state.solver.frame

        # Source parameters
        self.source_start = source_start

        if source_end == -1:
            source_end = self.state.MAX_CALLDATA_SIZE - 1

        self.source_end = source_end
        self.source_size = self.source_end - self.source_start

        # Convert to solver types
        self.source_start = BVV(self.source_start, 256)
        self.source_end   = BVV(self.source_end, 256)
        self.source_size  = BVV(self.source_size, 256)

        assert(is_concrete(self.source_start) and is_concrete(self.source_end))

        # Check if the bytes marked as tainted are symbolic or not.
        # If they are initialized concretely, we considerably limit the 
        # amount of solution we can get later. This can impact the
        # taint analysis if not used carefully.
        tainted_concrete_guard = False
        for index in range(source_start, source_end+1):
            if is_concrete(self.state.calldata[BVV(index,256)]):
                tainted_concrete_guard = True
        if tainted_concrete_guard:
            self.log.warning(f"Some CALLDATA bytes are tainted, but initialized with concrete data.")
    
        # Get an instance for the sha resolver
        self.sha_resolver = ShaResolver(self.state, sha_deps=sha_deps)
        self.sha_resolver.detect_sha_dependencies()
        self.state_has_shas = True if len(self.sha_resolver.sha_deps) != 0 else False

        self.log.debug(f"Taint applied to CALLDATA[{self.source_start}:{self.source_end}] (size: {self.source_size})")

        self.is_tainted = False
    
    def reg_to_human(self, val):
        return hex(bv_unsigned_value(val))

    def mem_to_human(self, val, size):
        return bv_unsigned_value(val).to_bytes(bv_unsigned_value(size), 'big').hex()

    def run(self):

        self.log.info("Starting CALLDATA to tagetContract taint analysis")

        calldata_sol = self.state.solver.eval_memory_at(self.state.calldata, self.source_start, self.source_size, raw=True)

        self.log.info(f"Using CALLDATA[{self.source_start.value}:{self.source_end.value}] {self.mem_to_human(calldata_sol, self.source_size)}")

        whole_calldata = self.state.solver.eval_memory(self.state.calldata, BVV(self.state.MAX_CALLDATA_SIZE,256), raw=True)
        self.log.debug(f"{self.mem_to_human(whole_calldata, BVV(self.state.MAX_CALLDATA_SIZE,256))}")

        # Fix this solution in a new frame (+1)
        self.state.solver.push()
        self.state.add_constraint(Equal(calldata_sol, self.state.calldata.readn(self.source_start, self.source_size)))

        # Resolve SHAs if any (this also fix the solutions in the solver in a new frame) (+1)
        if self.state_has_shas:
            self.sha_resolver.fix_shas()
        
        # Get solution
        targetContract_raw = self.state.solver.eval(self.state.registers[self.state.curr_stmt.arg2_var], raw=True)
        self.log.info(f"targetContract at CALL is: {self.reg_to_human(targetContract_raw)}")

        # removes sha constraints (-1)
        if self.state_has_shas:
            self.state.solver.pop()

        # remove constraint for CALLDATA
        self.state.solver.pop()

        # HERE FRAMEs ARE CLEAN (0)
        assert(self.state.solver.frame == 0 )

        # Add frame to avoid previous CALLDATA solution (+1)
        self.state.solver.push()
        
        # We don't want the previous one
        self.state.add_constraint(NotEqual(calldata_sol, self.state.calldata.readn(self.source_start, self.source_size)))
        
        if self.state_has_shas:
            self.sha_resolver.clear_solutions()
            self.sha_resolver.fix_shas() # (+1)

        # If this is not SAT, we cannot reach the same state with a different CALLDATA!
        if not self.state.solver.is_sat():
            self.log.fatal("Cannot reach same state with a different CALLDATA!")
        else:            
            if self.state.solver.is_formula_true(Equal(targetContract_raw, self.state.registers[self.state.curr_stmt.arg2_var])):
                self.log.info(f"{bcolors.BLUEBG}targetContract at CALL does NOT depend from source!{bcolors.ENDC}")
            else:
                self.log.info(f"{bcolors.REDBG}targetContract at CALL depends from source!{bcolors.ENDC}")
                # Let's create a solution for that :) 
                self.state.add_constraint(NotEqual(targetContract_raw, self.state.registers[self.state.curr_stmt.arg2_var]))
                new_calldata = self.state.solver.eval_memory(self.state.calldata, BVV(self.state.MAX_CALLDATA_SIZE,256), raw=True)
                new_targetContract_raw = self.state.solver.eval(self.state.registers[self.state.curr_stmt.arg2_var], raw=True)
                
                self.log.info(f"Possible solution:")
                self.log.info(f" CALLDATA: {self.mem_to_human(new_calldata, BVV(self.state.MAX_CALLDATA_SIZE,256))}")
                self.log.info(f"targetContract at CALL: {self.reg_to_human(new_targetContract_raw)}")
                self.is_tainted = True
        
        # DISCUSSION/NOTE: Shall we keep the constraints over the targetContract to evaluate the 
        # funcTarget?
        # As of now, let's pop everything.
        if self.state_has_shas:
            self.state.solver.pop() # (-1)
        self.state.solver.pop() # (-1)


