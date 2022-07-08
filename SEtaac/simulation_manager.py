import hashlib
import logging
import networkx
import os
import sys
from typing import Callable

from SEtaac.utils.exceptions import VMException
from SEtaac.state import SymbolicEVMState

log = logging.getLogger(__name__)
log.setLevel(logging.INFO)

class SimgrViz(object):
    def __init__(self):
        self._simgGraph = networkx.DiGraph()
        self.timestamp = 0
        self._first_instruction = None

    def get_state_hash(self, state):
        h = hashlib.sha256()
        h.update(str(state.pc).encode("utf-8"))
        h.update(str(state.callstack).encode("utf-8"))
        h.update(str(state.instruction_count).encode("utf-8"))
        h.update(str(state.gas).encode("utf-8"))
        h.update('\n'.join([x for x in state.registers.keys()]).encode("utf-8"))
        h_hexdigest = h.hexdigest()
        state._id = h_hexdigest
        return str(h_hexdigest)

    def add_node(self, state):
        state_id = self.get_state_hash(state)
        if state_id in self._simgGraph:
            return state_id
        self._simgGraph.add_node(state_id)
        self._simgGraph.nodes[state_id]['timestamp'] = str(self.timestamp)
        self._simgGraph.nodes[state_id]['pc'] = state.pc
        self._simgGraph.nodes[state_id]['csts'] = '\n'.join([str(x.dump()) for x in state.constraints])
        self.timestamp += 1
        return state_id
    
    def add_edge(self, new_state_id, parent_state_id):
        self._simgGraph.add_edge(new_state_id, parent_state_id)

    def dump_graph(self):
        s = 'digraph g {\n'
        s += '\tsplines=ortho;\n'
        s += '\tnode[fontname="courier"];\n'

        for node_id in self._simgGraph.nodes:
            node = self._simgGraph.nodes[node_id]
            
            shape = 'box'       

            s += '\t\"{}\" [shape={},label='.format(node_id[:10], shape)
            s += '<ts:{}<br align="left"/>'.format(node["timestamp"])
            s += '<br align="left"/>pc:{}'.format(node["pc"])
            s += '<br align="left"/>csts:{}'.format(node["csts"])
            s += '<br align="left"/>>];\n'  
        
        s += '\n'
        
        for edge in self._simgGraph.edges:
            start = edge[0][:10]
            end = edge[1][:10]
            s += '\t\"%s\" -> \"%s\";\n' % (end, start)
        
        s += '}'
        
        with open("./simgr_viz.dot", "w") as simgrviz_file:
            simgrviz_file.write(s)

class SimulationManager:
    def __init__(self, entry_state: SymbolicEVMState, keep_predecessors: int = 0, debug=False):
        self.keep_predecessors = keep_predecessors
        self.error = list()
        self._halt = False

        self.insns_count = 0

        self.debug = debug

        if debug:
            self.simgrViz = SimgrViz()

        # initialize empty stashes
        self._stashes = {
            'active': [],
            'deadended': [],
            'found': [],
            'pruned': []
        }

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

    def step(self):
        log.debug('-' * 30)
        new_active = list()
        for state in self.active:
            successors = self.single_step_state(state)
            new_active += successors
        self._stashes['active'] = new_active

        # migrate common constraints to solver
        # todo: this is a very hacky way to use incremental solving as much as possible
        common_constraints = set.intersection(*[set(s.constraints) for s in self.active])
        from SEtaac.utils.solver.shortcuts import _SOLVER
        # Common constraints are becoming 
        _SOLVER.add_assertions(list(common_constraints))
        for s in self.states:
            s.constraints = list(set(s.constraints)-common_constraints)

    def single_step_state(self, state: SymbolicEVMState):
        log.debug('Stepping {}'.format(state))
        log.debug(state.curr_stmt)
        old_pc = state.pc 

        successors = list()

        if self.debug:
            parent_state_id = self.simgrViz.add_node(state)
         
        try:
            successors += state.curr_stmt.handle(state)
        except Exception as e:
            log.exception(f"Something went wrong while stepping {state}")
            state.error = e
            state.halt = True
            successors += [state]

        if self.debug:
            for succ in successors:
                child_state_id = self.simgrViz.add_node(succ)
                log.debug("Stepping {} produced {}".format(old_pc, succ._pc))
                self.simgrViz.add_edge(child_state_id, parent_state_id)
        return successors

    def run(self, find: Callable[[SymbolicEVMState], bool] = lambda s: False,
            prune: Callable[[SymbolicEVMState], bool] = lambda s: False,
            find_all=False):
        """
        Run the simulation manager, until the `find` condition is met. The analysis will stop when there are no more
        active states or some states met the `find` condition (these will be moved to the found stash)
        :param find: Function that will be called after each step. The matching states will be moved to the found stash
        :param prune: Function that will be called after each step. The matching states will be moved to the pruned stash
        :return: None
        """

        try:
            while len(self.active) > 0:
                if len(self.found) > 0 and not find_all:
                    break
                elif self._halt:
                    break

                self.step()
                self.insns_count += 1

                self.move(from_stash='active', to_stash='found', filter_func=find)
                self.move(from_stash='active', to_stash='deadended', filter_func=lambda s: s.halt)
                self.move(from_stash='active', to_stash='pruned', filter_func=prune)
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
