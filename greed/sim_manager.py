import logging
import os
import sys
from typing import Callable, List, Optional, TYPE_CHECKING, TypedDict

from greed import options
from greed.state import SymbolicEVMState

if TYPE_CHECKING:
    from greed.exploration_techniques import ExplorationTechnique
    from greed.project import Project
    _STASHES_TYPE = TypedDict('Stashes', {
        'active': List[SymbolicEVMState],
        'deadended': List[SymbolicEVMState],
        'found': List[SymbolicEVMState],
        'pruned': List[SymbolicEVMState],
        'unsat': List[SymbolicEVMState],
        'errored': List[SymbolicEVMState]
    })


log = logging.getLogger(__name__)


class SimulationManager:
    """
    This class is the main class for running the symbolic execution.
    The simulation manager is responsible for keeping track of the states,
    and for moving them between the different stashes according to the employed
    exploration techniques.
    """
    project: "Project"
    _techniques: List["ExplorationTechnique"]
    stashes: "_STASHES_TYPE"
    insns_count: int
    error: List[str]

    def __init__(self, entry_state: SymbolicEVMState, project: "Project"):
        """
        Args:
            entry_state: The entry state of the simulation manager
            project: The greed project
        """
        self.project = project
        self._techniques = []

        # initialize empty stashes
        self.stashes = {
            'active': [],
            'deadended': [],
            'found': [],
            'pruned': [],
            'unsat': [],
            'errored': []
        }

        self.insns_count = 0
        self.error = list()

        self.active.append(entry_state)

    def set_error(self, s: str):
        """
        Set an error to the simulation manager
        """
        log.error(f'[ERROR] {s}')
        self.error += [s]

    @property
    def states(self) -> List[SymbolicEVMState]:
        """
        Returns:
            All the states in the simulation manager
        """
        return sum(self.stashes.values(), [])

    @property
    def active(self) -> List[SymbolicEVMState]:
        """
        Returns:
            All the active states
        """
        return self.stashes['active']

    @property
    def deadended(self) -> List[SymbolicEVMState]:
        """
        Returns:
            All the deadended states (halted states)
        """
        return self.stashes['deadended']

    @property
    def found(self) -> List[SymbolicEVMState]:
        """
        Returns:
            All the found states (states that met the `find` condition)
        """
        return self.stashes['found']

    @property
    def one_active(self) -> Optional[SymbolicEVMState]:
        """
        Returns:
            First element of the active stash, or None if the stash is empty
        """
        if len(self.stashes['active']) > 0:
            return self.stashes['active'][0]
        else:
            return None

    @property
    def one_deadended(self) -> Optional[SymbolicEVMState]:
        """
        Returns:
            First element of the deadended stash, or None if the stash is empty
        """
        if len(self.stashes['deadended']) > 0:
            return self.stashes['deadended'][0]
        else:
            return None

    @property
    def one_found(self) -> Optional[SymbolicEVMState]:
        """
        Returns:
            First element of the found stash, or None if the stash is empty
        """
        if len(self.stashes['found']) > 0:
            return self.stashes['found'][0]
        else:
            return None

    def use_technique(self, technique: "ExplorationTechnique"):
        """
        Install an exploration technique in the simulation manager.
        """
        technique.project = self.project
        technique.setup(self)
        self._techniques.append(technique)
        return technique

    def move(self, from_stash: str, to_stash: str, filter_func: Callable[[SymbolicEVMState], bool] = lambda s: True):
        """
        Move all the states that meet the filter_func condition from from_stash to to_stash
        Args:
            from_stash: Source stash
            to_stash: Destination Stash
            filter_func: A function that discriminates what states should be moved
        """
        for s in list(self.stashes[from_stash]):
            if filter_func(s):
                self.stashes[from_stash].remove(s)
                self.stashes[to_stash].append(s)

    def step(self, find: Callable[[SymbolicEVMState], bool] = lambda s: False,
                   prune: Callable[[SymbolicEVMState], bool] = lambda s: False):
        """
        Step the simulation manager, i.e., step all the active states.
        Args:
            find: A function that discriminates what states should be moved to the found stash
            prune: A function that discriminates what states should be moved to the pruned stash
        """
        log.debug('-' * 30)
        new_active = list()
        # Let the techniques manipulate the stashes
        for tech in self._techniques:
            self.stashes = tech.check_stashes(self, self.stashes)

        # Let's step the active!
        for state in self.active:
            try:
                successors = self.single_step_state(state)
            except Exception as e:
                log.exception(f"Something went wrong while generating successor for {state}")
                state.error = e
                state.halt = True
                successors = [state]
            new_active += successors

        self.stashes['active'] = new_active

        self.insns_count += 1

        self.move(from_stash='active', to_stash='found', filter_func=find)
        self.move(from_stash='active', to_stash='errored', filter_func=lambda s: s.error != None)
        self.move(from_stash='active', to_stash='deadended', filter_func=lambda s: s.halt)
        self.move(from_stash='active', to_stash='pruned', filter_func=prune)

        if not options.LAZY_SOLVES:
            self.move(from_stash='active', to_stash='unsat', filter_func=lambda s: not s.solver.is_sat())
        self.move(from_stash='found', to_stash='unsat', filter_func=lambda s: not s.solver.is_sat())

        for s in self.stashes['pruned'] + self.stashes['unsat'] + self.stashes['errored']:
            s.solver.dispose_context()

    def single_step_state(self, state: SymbolicEVMState) -> List[SymbolicEVMState]:
        """
        Step a single state (calculate its successors)
        Args:
            state: The state to step
        Returns:
            The successors of the state
        Raises:
            Exception: If something goes wrong while generating the successors
        """
        log.debug(f"Stepping {state}")
        log.debug(state.curr_stmt)

        # Some inspect capabilities, uses the plugin.
        if hasattr(state, "inspect"):
            # Trigger breakpoints on specific stmt_id
            if state.pc in state.inspect.breakpoints_stmt_ids.keys():
                state.inspect.breakpoints_stmt_ids[state.pc](self, state)
            # Trigger breakpoints on all the stmt with that name
            if state.curr_stmt.__internal_name__ in state.inspect.breakpoints_stmt.keys():
                state.inspect.breakpoints_stmt[state.curr_stmt.__internal_name__](self, state)
        successors = list()

        # Let exploration techniques manipulate the state
        # that is going to be handled
        state_to_step = state
        for t in self._techniques:
            state_to_step = t.check_state(self, state_to_step)

        # Finally step the state
        try:
            successors += state.curr_stmt.handle(state)
        except Exception as e:
            log.exception(f"Something went wrong while generating successor for {state}")
            state.error = e
            state.halt = True
            successors += [state]

        # Let exploration techniques manipulate the successors
        for t in self._techniques:
            successors = t.check_successors(self, successors)

        return successors

    def run(self, find: Callable[[SymbolicEVMState], bool] = lambda s: False,
            prune: Callable[[SymbolicEVMState], bool] = lambda s: False,
            find_all=False):
        """
        Run the simulation manager, until the `find` condition is met.
        The analysis will stop when there are no more active states, some states met the `find` condition
        (these will be moved to the found stash), or the exploration techniques are done.
        If no ET are plugged, the default searching strategy is BFS.
        When techniques are plugged, their methods are executed following the same order they were plugged.

        e.g., assuming we have T1 and T2.
                T1(check_stashes) -> T2(check_stashes) -> T1(check_state) -> T2(check_state)
                    -> T1(check_successors) -> T2(check_successors)

        Args:
            find: Function that will be called after each step. The matching states will be moved to the found stash
            prune: Function that will be called after each step. The matching states will be moved to the pruned stash
            find_all: If True, the analysis will continue until all the ET meet the `find` condition
        Raises:
            Exception: If something goes wrong while stepping the simulation manager
        """
        try:
            # We iterate until we have active states,
            # OR, if any of the ET is not done.
            while len(self.active) > 0 or (self._techniques != [] and
                                            not(all([t.is_complete(self) for t in self._techniques]))):

                if len(self.found) > 0 and not find_all:
                    break

                self.step(find, prune)

        except Exception as e:
            exc_type, exc_obj, exc_tb = sys.exc_info()
            fname = os.path.split(exc_tb.tb_frame.f_code.co_filename)[1]

            log.exception(f'Exception while stepping the Simulation Manager')
            self.set_error(f'{exc_type.__name__} at {fname}:{exc_tb.tb_lineno}')
            sys.exit(1)

    def findall(self, find: Callable[[SymbolicEVMState], bool] = lambda s: False,
            prune: Callable[[SymbolicEVMState], bool] = lambda s: False):
        """
        Run the simulation manager, until the `find` condition of all the ET is met.
        Args:
            find: Function that will be called after each step. The matching states will be moved to the found stash
            prune: Function that will be called after each step. The matching states will be moved to the pruned stash
        Yield:
            The found states
        Raises:
            Exception: If something goes wrong while stepping the simulation manager
        """
        try:
            while len(self.active) > 0 or (self._techniques != [] and not(all([t.is_complete(self) for t in self._techniques]))):
                self.step(find, prune)

                for found in self.found:
                    yield found
                self.stashes["found"] = list()

        except Exception as e:
            exc_type, exc_obj, exc_tb = sys.exc_info()
            fname = os.path.split(exc_tb.tb_frame.f_code.co_filename)[1]

            log.exception(f'Exception while stepping the Simulation Manager')
            self.set_error(f'{exc_type.__name__} at {fname}:{exc_tb.tb_lineno}')
            sys.exit(1)


    def __str__(self):
        stashes_str = [f'{len(stash)} {stash_name}'  # {[s for s in stash]}'
                       for stash_name, stash in self.stashes.items() if len(stash)]
        errored_count = len([s for s in self.states if s.error])
        stashes_str += [f'({errored_count} errored)']
        reverted_count = len([s for s in self.states if s.revert])
        stashes_str += [f'({reverted_count} reverted)']
        return f'<SimulationManager[{self.insns_count}] with {", ".join(stashes_str)}>'

    def __repr__(self):
        return self.__str__()
