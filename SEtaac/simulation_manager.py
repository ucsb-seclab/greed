import logging
import os
import sys


class SimulationManager:
    def __init__(self, entry_state, keep_predecessors=0):
        self.keep_predecessors = keep_predecessors
        self.error = list()
        self._halt = False

        self.insns_count = 0

        # initialize empty stashes
        self._stashes = {
            'active': [],
            'deadended': [],
            'found': [],
            'pruned': []
        }

        self.active.append(entry_state)

    def set_error(self, s):
        logging.error(f'[ERROR] {s}')
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

    def move(self, from_stash, to_stash, filter_func=lambda s: True):
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

    # def step(self, n=1):
    #     """
    #     Perform n steps (default is 1), after each step move all the halted states to the deadended stash
    #     :param n: Number of steps
    #     :return: None
    #     """
    #     for _ in range(n):
    #         for state in list(self.active):
    #             try:
    #                 state.step()
    #             except Exception as e:
    #                 exc_type, exc_obj, exc_tb = sys.exc_info()
    #                 fname = os.path.split(exc_tb.tb_frame.f_code.co_filename)[1]
    #
    #                 self.set_error(f'{exc_type.__name__} at {fname}:{exc_tb.tb_lineno}')
    #                 state.error = e.__class__
    #
    #         self.move(from_stash='active', to_stash='deadended', filter_func=lambda s: s.halt or s.error)


    def step(self):
        new_active = list()
        for state in self.active:
            successors = self.single_step_state(state)
            new_active += successors
        self._stashes['active'] = new_active

    def single_step_state(self, state):
        successors = state.curr_stmt.handle(state)

        # todo: somewhere we should take care of stuff that used to be in state.step()
        # state.trace.append(state.pc)
        # state.instruction_count += 1
        # state.gas -= ins.gas

        return successors

    def run(self, find=lambda s: False):
        """
        Run the simulation manager, until the `find` condition is met. The analysis will stop when there are no more
        active states or some states met the `find` condition (these will be moved to the found stash)
        :param find: Function that will be called after each step. The matching states will be moved to the found stash
        :return: None
        """

        try:
            while len(self.active) > 0 and len(self.found) == 0 and not self._halt:
                self.move(from_stash='active', to_stash='found', filter_func=find)

                self.step()

                self.insns_count += 1
        except Exception as e:
            exc_type, exc_obj, exc_tb = sys.exc_info()
            fname = os.path.split(exc_tb.tb_frame.f_code.co_filename)[1]

            logging.exception(f'Exception while stepping the Simulation Manager')
            self.set_error(f'{exc_type.__name__} at {fname}:{exc_tb.tb_lineno}')

    def __str__(self):
        stashes_str = [f'{len(stash)} {stash_name}'  # {[s for s in stash]}'
                       for stash_name, stash in self._stashes.items() if len(stash)]
        errored_count = len([s for stash_name, stash in self._stashes.items() if len(stash) for s in stash if s.error])
        stashes_str += [f'({errored_count} errored)']
        return f'<SimulationManager[{self.insns_count}] with {", ".join(stashes_str)}>'

    def __repr__(self):
        return self.__str__()