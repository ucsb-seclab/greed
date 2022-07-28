import hashlib
import logging
import networkx
import os
import sys
from typing import Callable

from SEtaac.utils.exceptions import VMException
from SEtaac.state import SymbolicEVMState
from SEtaac import options

log = logging.getLogger(__name__)


class SimulationManager:
    def __init__(self, entry_state: SymbolicEVMState, project):
        self._project = project
        self._halt = False
        self._techniques = []

        # initialize empty stashes
        self._stashes = {
            'active': [],
            'deadended': [],
            'found': [],
            'pruned': []
        }

        self.insns_count = 0
        self.error = list()

        self.active.append(entry_state)

    def set_error(self, s: str):
        log.error(f'[ERROR] {s}')
        self.error += [s]

    @property
    def states(self):
        """
        :return: All the states
        """
        return sum(self._stashes.values(), [])

    @property
    def active(self):
        """
        :return: Active stash
        """
        return self._stashes['active']

    @property
    def deadended(self):
        """
        :return: Deadended stash
        """
        return self._stashes['deadended']

    @property
    def found(self):
        """
        :return: Found stash
        """
        return self._stashes['found']

    @property
    def one_active(self):
        """
        :return: First element of the active stash, or None if the stash is empty
        """
        if len(self._stashes['active']) > 0:
            return self._stashes['active'][0]
        else:
            return None

    @property
    def one_deadended(self):
        """
        :return: First element of the deadended stash, or None if the stash is empty
        """
        if len(self._stashes['deadended']) > 0:
            return self._stashes['deadended'][0]
        else:
            return None

    @property
    def one_found(self):
        """
        :return: First element of the found stash, or None if the stash is empty
        """
        if len(self._stashes['found']) > 0:
            return self._stashes['found'][0]
        else:
            return None

    def use_technique(self, tech):
        # Pre-check 
        if not isinstance(tech, ExplorationTechnique):
            raise Exception
        needed_methods = {"setup", "check_stashes", "check_state", "check_successors"}
        # Check if we have all the required methods 
        tech_methods = set(x for x in dir(tech) if x.startswith('check_') is True or x == "setup")
        if len(needed_methods.difference(tech_methods)) != 0:
            raise Exception("The ET you are trying to install is missing methods")
        
        # All good, let's install it.
        tech.project = self._project
        tech.setup(self)
        self._techniques.append(tech)
        return tech

    def move(self, from_stash: str, to_stash: str, filter_func: Callable[[SymbolicEVMState], bool] = lambda s: True):
        """
        Move all the states that meet the filter_func condition from from_stash to to_stash
        :param from_stash: Source stash
        :param to_stash: Destination Stash
        :param filter_func: A function that discriminates what states should be moved
        :return: None
        """
        for s in list(self._stashes[from_stash]):
            if filter_func(s):
                self._stashes[from_stash].remove(s)
                self._stashes[to_stash].append(s)

    def step(self, find: Callable[[SymbolicEVMState], bool] = lambda s: False,
                   prune: Callable[[SymbolicEVMState], bool] = lambda s: False):
        log.debug('-' * 30)
        new_active = list()
        
        # Let the techniques manipulate the stashes
        for tech in self._techniques: 
            self._stashes = tech.check_stashes(self._stashes)
        
        # Let's step the active!
        for state in self.active:
            successors = self.single_step_state(state)
            new_active += successors
        
        self._stashes['active'] = new_active

        self.insns_count += 1

        self.move(from_stash='active', to_stash='found', filter_func=find)
        self.move(from_stash='active', to_stash='deadended', filter_func=lambda s: s.halt)
        self.move(from_stash='active', to_stash='pruned', filter_func=prune)

    def single_step_state(self, state: SymbolicEVMState):
        log.debug(f"Stepping {state}")
        log.debug(state.curr_stmt)

        old_pc = state.pc

        if state.pc in state.breakpoints.keys():
            log.warning("⚡ Triggered breakpoint at {}".format(state.pc))
            state.breakpoints[state.pc](state)

        successors = list()
        
        # Let exploration techniques manipulate the state
        # that is going to be handled
        state_to_step = state
        for t in self._techniques: 
            state_to_step = t.check_state(state_to_step)

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
            successors = t.check_successors(successors)
        
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

        :param find: Function that will be called after each step. The matching states will be moved to the found stash
        :param prune: Function that will be called after each step. The matching states will be moved to the pruned stash
        :return: None
        """

        try:
            # We iterate until we have active states, 
            # OR, if any of the ET is not done.
            while len(self.active) > 0 or (self._techniques != [] and 
                                            not(all([t.is_complete(self) for t in self._techniques]))):
                
                if len(self.found) > 0 and not find_all:
                    break
                elif self._halt:
                    break
                
                self.step(find, prune)

        except Exception as e:
            exc_type, exc_obj, exc_tb = sys.exc_info()
            fname = os.path.split(exc_tb.tb_frame.f_code.co_filename)[1]

            log.exception(f'Exception while stepping the Simulation Manager')
            self.set_error(f'{exc_type.__name__} at {fname}:{exc_tb.tb_lineno}')
            exit(1)

    def __str__(self):
        stashes_str = [f'{len(stash)} {stash_name}'  # {[s for s in stash]}'
                       for stash_name, stash in self._stashes.items() if len(stash)]
        errored_count = len([s for s in self.states if s.error])
        stashes_str += [f'({errored_count} errored)']
        reverted_count = len([s for s in self.states if s.revert])
        stashes_str += [f'({reverted_count} reverted)']
        return f'<SimulationManager[{self.insns_count}] with {", ".join(stashes_str)}>'

    def __repr__(self):
        return self.__str__()


from .exploration_techniques import ExplorationTechnique