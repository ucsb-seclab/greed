import logging

from SEtaac.solver.shortcuts import *
from sha_resolver import ShaResolver
from utils import bcolors



class CalldataToFuncTarget():
    def __init__(self, state):
        
        self.state = state
        
        assert(self.state.curr_stmt.__internal_name__ == "CALL")

        self.log = logging.getLogger("CalldataToFuncTarget")
        self.log.setLevel(logging.DEBUG)

        self.starting_frame = self.state.solver.frame

        # Get an instance for the sha resolver
        self.sha_resolver = ShaResolver(self.state)
        
        self.state_has_shas = True if len(self.state.sha_observed) != 0 else False

        self.is_tainted = None

    def mem_to_human(self, val, size):
        return bv_unsigned_value(val).to_bytes(bv_unsigned_value(size), 'big').hex()
    
    def run(self):
        
        assert(self.state.solver.frame==0)

        self.log.info("Starting CALLDATA to funcTarget taint analysis")

        calldata_sol = self.state.solver.eval_memory(self.state.calldata, BVV(self.state.MAX_CALLDATA_SIZE,256), raw=True)

        self.log.debug(f"{self.mem_to_human(calldata_sol, BVV(self.state.MAX_CALLDATA_SIZE,256))}")

        # Fix CALLDATA solution in a new frame (+1)
        self.state.solver.push()
        
        assert(self.state.solver.frame == 1)
        self.state.add_constraint(Equal(calldata_sol, self.state.calldata.readn(BVV(0,256), BVV(self.state.MAX_CALLDATA_SIZE,256))))

        # Resolve SHAs if any (this also fix the solutions in the solver in a new frame) (+1)
        if self.state_has_shas:
            if not self.sha_resolver.fix_shas():
                self.state.solver.pop_all() # Clean frames (0)
                assert(self.state.solver.frame==0)
                # If we cannot fix SHAs, let's call it a day
                return
        else:
            assert(self.state.solver.frame==1)

        # Get solution for CALL parameters
        mem_offset_call_raw = self.state.solver.eval(self.state.registers[self.state.curr_stmt.arg4_var], raw=True)
        mem_offset_call = bv_unsigned_value(mem_offset_call_raw)
        self.log.debug(f"Using {mem_offset_call} as argOffset for CALL state")
        
        # Here we consider only the first 4 bytes
        mem_argSize_raw = BVV(4, 256)

        # Maybe make sure the argSize is at least greater than 4 for every possible solution?
        #assert(self.state.solver.is_formula_true(BV_UGT(mem_argSize_raw, BVV(4,256))))

        self.log.debug(f"Using only 4 as argSize for CALL state (wanna check only target func)")

        # Fix the offset (+1)
        self.state.solver.push()
        self.state.add_constraint(Equal(mem_offset_call_raw, self.state.registers[self.state.curr_stmt.arg4_var]))

        mem_at_call_raw = self.state.solver.eval_memory_at(self.state.memory, mem_offset_call_raw, mem_argSize_raw, raw=True)
        mem_at_call = bv_unsigned_value(mem_at_call_raw)
        self.log.debug(f"funcTarget at CALL is: 0x{self.mem_to_human(mem_at_call_raw, mem_argSize_raw)}")

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

        for target_byte in range(4,self.state.MAX_CALLDATA_SIZE):
            
            #self.log.debug(f"Flipping byte {target_byte}")

            # Flip all the bytes but the target one
            self.state.solver.push() # Adding the current sol +1 frame
            assert(self.state.solver.frame == 1)
            self.sha_resolver.clear_solutions()
            
            for x,b in zip(range(0, self.state.MAX_CALLDATA_SIZE), 
                                    bv_unsigned_value(calldata_sol).to_bytes(self.state.MAX_CALLDATA_SIZE, 'big')):
                
                # The current target byte to flip is kept symbolic, the rest is set equal to the previous
                # solution.
                if x != target_byte:
                    #self.log.debug(f"calldata[{x}]={hex(b)}")
                    self.state.add_constraint(Equal(self.state.calldata[BVV(x,256)], BVV(b,8)))
                else:
                    self.state.add_constraint(NotEqual(self.state.calldata[BVV(x,256)], BVV(b,8)))
                    #self.log.debug(f"calldata[{x}]!={hex(b)}")
                    #self.log.warning(f"Skipping byte {target_byte}, leaving it symbolic!")
            
            if not self.state.solver.is_sat():
                #self.log.debug("UNSAT state")
                pass
            else:
                if self.state_has_shas:
                    if not self.sha_resolver.fix_shas(): # (+1)
                        self.state.solver.pop_all() # Clean frames (0)
                        assert(self.state.solver.frame==0)
                
                # If this is not SAT, we cannot reach the same state with a different CALLDATA!
                if not self.state.solver.is_sat():
                    self.log.fatal("Cannot reach same state with a different CALLDATA!")
                else:
                    # DISCUSSION: at this point, if the state is sat, it means that there exist CALLDATA values (different from the 
                    # previous one) that respect the SHAs solutions we just set.
                    
                    # DISCUSSION: if the memory at CALL is ALWAYS equal to the mem calculated before ( i.e., a different CALLDATA cannot change
                    # the outcome of the bytes at this location, then we conclude that the mem_at_call is not dependent from the CALLDATA bytes)
                    if self.state.solver.is_formula_sat(Equal(mem_at_call_raw, self.state.memory.readn(mem_offset_call_raw, BVV(4,256)))):
                        #self.log.info(f"{bcolors.BLUEBG}funcTarget at CALL does NOT depend from source!{bcolors.ENDC}")
                        self.is_tainted = False
                    else:
                        # DISCUSSION: in this case it means that there exist a possibility for a different CALLDATA to create a different 
                        # mem_at_call, hence, we conclude this is tainted!
                        self.log.info(f"{bcolors.PINKBG}funcTarget at CALL depends from source byte {target_byte}!{bcolors.ENDC}")
                        # Let's create a solution for that :) 
                        self.state.add_constraint(NotEqual(mem_at_call_raw, self.state.memory.readn(mem_offset_call_raw, mem_argSize_raw)))
                        new_calldata = self.state.solver.eval_memory(self.state.calldata, BVV(self.state.MAX_CALLDATA_SIZE,256), raw=True)
                        new_memory_at_call = self.state.solver.eval_memory_at(self.state.memory, mem_offset_call_raw, mem_argSize_raw, raw=True)
                        #self.log.debug(f"Possible solution:")
                        #self.log.debug(f" CALLDATA: {self.mem_to_human(new_calldata, BVV(self.state.MAX_CALLDATA_SIZE,256))}")
                        #self.log.debug(f"funcTarget at CALL: 0x{self.mem_to_human(new_memory_at_call, mem_argSize_raw)}")
                        self.is_tainted = True
                        break

            self.state.solver.pop_all()
            assert(self.state.solver.frame==0)

        if not self.is_tainted:
            self.log.info(f"{bcolors.BLUEBG}funcTarget at CALL does NOT depend from source!{bcolors.ENDC}")

        # Leave this clean before exiting
        self.state.solver.pop_all()
                

class CalldataToContractTarget():
    def __init__(self, state):
        self.state = state
        
        assert(self.state.curr_stmt.__internal_name__ == "CALL")

        self.log = logging.getLogger("CalldataToContractTarget")
        self.log.setLevel(logging.DEBUG)

        self.starting_frame = self.state.solver.frame
    
        # Get an instance for the sha resolver
        self.sha_resolver = ShaResolver(self.state)
        self.state_has_shas = True if len(self.state.sha_observed) != 0 else False

        self.is_tainted = False
    
    def reg_to_human(self, val):
        return hex(bv_unsigned_value(val))

    def mem_to_human(self, val, size):
        return bv_unsigned_value(val).to_bytes(bv_unsigned_value(size), 'big').hex()

    def run(self):

        self.log.info("Starting CALLDATA to targetContract taint analysis")
        
        calldata_sol = self.state.solver.eval_memory(self.state.calldata, BVV(self.state.MAX_CALLDATA_SIZE,256), raw=True)

        self.log.debug(f"{self.mem_to_human(calldata_sol, BVV(self.state.MAX_CALLDATA_SIZE,256))}")

        # Fix CALLDATA solution in a new frame (+1)
        self.state.solver.push()
        
        assert(self.state.solver.frame == 1)
        self.state.add_constraint(Equal(calldata_sol, self.state.calldata.readn(BVV(0,256), BVV(self.state.MAX_CALLDATA_SIZE,256))))

        # Resolve SHAs if any (this also fix the solutions in the solver in a new frame) (+1)
        if self.state_has_shas:
            if not self.sha_resolver.fix_shas():
                self.state.solver.pop_all() # Clean frames (0)
                assert(self.state.solver.frame==0)
                # If we cannot fix SHAs, let's call it a day
                return
        
        # Get solution
        targetContract_raw = self.state.solver.eval(self.state.registers[self.state.curr_stmt.arg2_var], raw=True)
        self.log.debug(f"targetContract at CALL is: {self.reg_to_human(targetContract_raw)}")

        # removes sha constraints (-1)
        if self.state_has_shas:
            self.state.solver.pop()

        # remove constraint for CALLDATA
        self.state.solver.pop()

        # HERE FRAMEs ARE CLEAN (0)
        assert(self.state.solver.frame == 0 )
        
        # Now we want to change the CALLDATA byte by byte to see if there is any change 
        # in the targetContract.
        # If the path constraints are remaining SAT and we observe a different value 
        # in the target contract, it means that input byte is influencing the 
        # memory at CALL.

        # This is keeping track of which byte of CALLDATA we are flipping 
  
              
        for target_byte in range(4,self.state.MAX_CALLDATA_SIZE):
            
            #self.log.debug(f"Flipping byte {target_byte}")

            # Flip all the bytes but the target one
            self.state.solver.push() # Adding the current sol +1 frame
            assert(self.state.solver.frame == 1)
            self.sha_resolver.clear_solutions()
            
            for x,b in zip(range(0, self.state.MAX_CALLDATA_SIZE), 
                                    bv_unsigned_value(calldata_sol).to_bytes(self.state.MAX_CALLDATA_SIZE, 'big')):
                
                # The current target byte to flip is kept symbolic, the rest is set equal to the previous
                # solution.
                if x != target_byte:
                    #self.log.debug(f"calldata[{x}]={hex(b)}")
                    self.state.add_constraint(Equal(self.state.calldata[BVV(x,256)], BVV(b,8)))
                else:
                    self.state.add_constraint(NotEqual(self.state.calldata[BVV(x,256)], BVV(b,8)))
                    #self.log.debug(f"calldata[{x}]!={hex(b)}")
                    #self.log.warning(f"Skipping byte {target_byte}, leaving it symbolic!")
            
            # We don't want the previous CALLDATA!
            #self.state.add_constraint(NotEqual(calldata_sol, self.state.calldata.readn(BVV(0,256), BVV(self.state.MAX_CALLDATA_SIZE,256))))
            if not self.state.solver.is_sat():
                #self.log.debug("UNSAT state")
                pass
            else:
                # If we are here, we found a byteflip that keeps the path constraints SAT
                #calldata_sol = self.state.solver.eval_memory(self.state.calldata, BVV(self.state.MAX_CALLDATA_SIZE,256), raw=True)
                if self.state_has_shas:
                    if not self.sha_resolver.fix_shas(): # (+1)
                        self.state.solver.pop_all() # Clean frames (0)
                        assert(self.state.solver.frame==0)
                        
                # Are we still SAT after we fixed the SHAs? 
                if not self.state.solver.is_sat():
                    self.log.fatal("Cannot reach same state with a different CALLDATA!")
                else:            
                    if self.state.solver.is_formula_sat(Equal(targetContract_raw, self.state.registers[self.state.curr_stmt.arg2_var])):
                        # WARNING: 
                        #    Here we MUST use is_formula_sat. 
                        #    Using is_formula_true is wrong because the solver can change other symbolic variables to make the formula false
                        #    and then detect a spurious dependency. (e.g, the CALLER flows in the contractTaget).
                        #    Using "is_formula_sat" we are basically askig ourself: "can we observe the same result as before with a 
                        #    CALLDATA flipped by one byte?". Of course this opens to false negatives, if flipping that byte CAN ALSO 
                        #    generate a different result later, but it's better to be conservative.
                        self.is_tainted = False
                    else:
                        self.log.info(f"{bcolors.PINKBG}targetContract at CALL depends from source byte {target_byte}!{bcolors.ENDC}")
                        # Let's create a solution for that :) 
                        self.state.add_constraint(NotEqual(targetContract_raw, self.state.registers[self.state.curr_stmt.arg2_var]))
                        new_calldata = self.state.solver.eval_memory(self.state.calldata, BVV(self.state.MAX_CALLDATA_SIZE,256), raw=True)
                        new_targetContract_raw = self.state.solver.eval(self.state.registers[self.state.curr_stmt.arg2_var], raw=True)    
                        self.log.debug(f"Possible solution:")
                        self.log.debug(f" CALLDATA: {self.mem_to_human(new_calldata, BVV(self.state.MAX_CALLDATA_SIZE,256))}")
                        self.log.debug(f" targetContract at CALL: {self.reg_to_human(new_targetContract_raw)}")
                        self.is_tainted = True
                        
                        # We can stop here for now.
                        break
                        
            self.state.solver.pop_all()
            assert(self.state.solver.frame==0)
        
        if not self.is_tainted:
            self.log.info(f"{bcolors.BLUEBG}targetContract at CALL does NOT depend from source!{bcolors.ENDC}")
    
        # Leave this clean before exiting
        self.state.solver.pop_all()