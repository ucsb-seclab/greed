import logging

from greed import options
from greed.solver.shortcuts import *
from greed.state_plugins import SimStatePlugin

log = logging.getLogger(__name__)


class SimStateSolver(SimStatePlugin):
    def __init__(self, partial_init=False):
        super(SimStateSolver, self).__init__()

        if partial_init:
            # Used for copy
            return

        if options.SOLVER == options.SOLVER_YICES2:
            from greed.solver import Yices2
            self._solver = Yices2()
        else:
            raise Exception(f"Unsupported solver {options.SOLVER}. Aborting.")

        # The solver backend
        assert(self._solver is not None)

        self._curr_frame_level = 0

        # Keep constraints organized in frames
        self._path_constraints = dict()
        self._memory_constraints = dict()
        
        self._path_constraints[0] = set()
        self._memory_constraints[0] = set()
    
    def _add_assertion(self, assertion):
        # Adding the constraint to the backend
        self._solver.add_assertion(assertion)

    def _add_assertions(self, assertions):
        # Adding the constraints to the backend
        self._solver.add_assertions(assertions)

    def push(self):
        self._curr_frame_level += 1
        self._path_constraints[self._curr_frame_level] = set()
        self._memory_constraints[self._curr_frame_level] = set()
        self._solver.push()
        return self._curr_frame_level

    def pop(self):
        if self._curr_frame_level == 0:
            log.fatal("Cannot pop() level 0 frame")
            return self._curr_frame_level
        else:
            del self._path_constraints[self._curr_frame_level]
            del self._memory_constraints[self._curr_frame_level]
            self._curr_frame_level -= 1
            self._solver.pop()
            return self._curr_frame_level
    
    def pop_all(self):
        while self._curr_frame_level != 0:
            self.pop()
    
    def add_path_constraints(self, constraint):
        self._path_constraints[self._curr_frame_level].add(constraint)
        self._add_assertion(constraint)

    def add_memory_constraints(self, constraint):
        self._memory_constraints[self._curr_frame_level].add(constraint)
        self._add_assertion(constraint)

    def simplify(self):
        for reg_var, reg_val in self.state.registers.items():
            if reg_val.is_simplified is False:
                if is_concrete(reg_val):
                    # simplify to basic BVV
                    self.state.registers[reg_var] = self.state.solver.eval(reg_val, raw=True)
                else:
                    reg_val_sol = self.state.solver.eval(reg_val, raw=True)
                    if not self.state.solver.is_formula_sat(NotEqual(reg_val, reg_val_sol)):
                        self.state.registers[reg_var] = reg_val_sol
                self.state.registers[reg_var].is_simplified = True
    @property
    def timed_out(self):
        return self._solver.timed_out

    @property
    def frame(self):
        return self._curr_frame_level
    
    @property
    def constraints(self):
        return self.constraints_at()

    @property
    def memory_constraints(self):
        return self.memory_constraints_at()
    
    @property
    def path_constraints(self):
        return self.path_constraints_at()

    # returns path constraints
    # If frame is None, returns ALL the currently active constraints,
    # otherwise, just return the constraints at a specific frame.
    def path_constraints_at(self, frame: int = None):
        if not frame:
            all_csts = [c_set for c_set in self._path_constraints.values()]
            return list(set().union(*all_csts))
        else:
            return list(self._path_constraints[frame])

    # returns memory constraints
    # If frame is None, returns ALL the currently active constraints,
    # otherwise, just return the constraints at a specific frame.
    def memory_constraints_at(self, frame=None):
        if not frame:
            all_csts = [c_set for c_set in self._memory_constraints.values()]
            return list(set().union(*all_csts))
        else:
            return list(self._memory_constraints[frame])
    
    # returns ALL the active constraints in all the stashes
    def constraints_at(self, frame=None):
        if not frame:
            all_path_csts = [c_set for c_set in self._path_constraints.values()]
            all_mem_csts = [c_set for c_set in self._memory_constraints.values()]
            all_path_csts.extend(all_mem_csts)
            return list(set().union(*all_path_csts))
        else:
            path_csts = self._path_constraints[frame]
            mem_csts = self._memory_constraints[frame]
            return list(path_csts.union(mem_csts))

    def dispose_context(self):
        if self._solver.solver.context:
            self._solver.solver.dispose()

    def is_concrete(self, term) -> bool:
        return self._solver.is_concrete(term)

    def is_sat(self) -> bool:
        return self._solver.is_sat()

    def is_unsat(self) -> bool:
        return self._solver.is_unsat()

    def is_formula_sat(self, formula) -> bool:
        return self._solver.is_formula_sat(formula)

    def are_formulas_sat(self, terms) -> bool:
        return self._solver.are_formulas_sat(terms)

    def is_formula_unsat(self, formula) -> bool:
        return self._solver.is_formula_unsat(formula)

    def is_formula_true(self, formula) -> bool:
        return self._solver.is_formula_true(formula)

    def is_formula_false(self, formula) -> bool:
        return self._solver.is_formula_false(formula)

    def eval(self, term, raw=False):
        return self._solver.eval(term, raw)
    
    def eval_memory(self, memory, length, raw=False):
        assert(self.is_concrete(length))
        memory_to_eval = memory.readn(BVV(0, 256), length)
        int_value = self.eval(memory_to_eval, raw=False)
        if raw is True:
            return BVV(int_value, bv_unsigned_value(length)*8)
        else:
            return f"{int_value:0{bv_unsigned_value(length)*2}x}"

    def eval_memory_at(self, array, offset, length, raw=False):
        assert(self.is_concrete(offset))
        assert(self.is_concrete(length))
        memory_to_eval = array.readn(offset, length)
        int_value = self.eval(memory_to_eval, raw=False)
        if raw is True:
            return BVV(int_value, bv_unsigned_value(length)*8)
        else:
            return f"{int_value:0{bv_unsigned_value(length)*2}x}"

    def copy(self):
        new_solver = SimStateSolver(partial_init=True)
        new_solver._solver = self._solver.copy()

        new_solver._curr_frame_level = 0
        new_solver._path_constraints = dict()
        new_solver._memory_constraints = dict()
        
        # Re-add all the constraints (Maybe one day Yices2 will do it for us with 
        # a full Context clone, as of now this is the "cloning dei poveri".
        while True:
            level = new_solver._curr_frame_level
            new_solver._path_constraints[level] = set(self._path_constraints[level])
            new_solver._add_assertions(new_solver._path_constraints[level])
            new_solver._memory_constraints[level] = set(self._memory_constraints[level])
            new_solver._add_assertions(new_solver._memory_constraints[level])
            
            if new_solver._curr_frame_level == self._curr_frame_level:
                break
            else: 
                # Add the next frame
                new_solver.push()

        return new_solver
    



