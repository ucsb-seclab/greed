import hashlib
import logging
import tempfile

import networkx

from . import ExplorationTechnique

log = logging.getLogger(__name__)


class SimgrViz(ExplorationTechnique):
    """
    This Exploration technique implements visualizes and dumps the simulation manager progress.
    The .dot output file will be logged during _dump_graph.
    """
    def __init__(self):
        super(SimgrViz, self).__init__()
        self._simgGraph = networkx.DiGraph()
        self.timestamp = 0
        self._first_instruction = None
        self.curr_parent_state_id = None

    def setup(self, simgr):
        return

    def check_stashes(self, simgr, stashes):
        return stashes

    def check_state(self, simgr, state):
        self.curr_parent_state_id = self._add_node(state)
        return state

    def check_successors(self, simgr, successors):
        assert self.curr_parent_state_id
        for succ in successors:
            child_state_id = self._add_node(succ)
            self._add_edge(child_state_id, self.curr_parent_state_id)
        return successors

    @staticmethod
    def _get_state_hash(state):
        """
        Calculate a unique hash for the state.
        """
        h = hashlib.sha256()
        h.update(str(state.pc).encode("utf-8"))
        h.update(str(state.callstack).encode("utf-8"))
        h.update(str(state.instruction_count).encode("utf-8"))
        h.update(str(state.gas).encode("utf-8"))
        h.update('\n'.join([x for x in state.registers.keys()]).encode("utf-8"))
        h_hexdigest = h.hexdigest()
        state._id = h_hexdigest
        return str(h_hexdigest)

    def _add_node(self, state):
        """
        Add a node to the graph.
        """
        state_id = self._get_state_hash(state)
        if state_id in self._simgGraph:
            return state_id
        self._simgGraph.add_node(state_id)
        self._simgGraph.nodes[state_id]['timestamp'] = str(self.timestamp)
        self._simgGraph.nodes[state_id]['pc'] = state.pc
        # if state.curr_stmt.__internal_name__ == "LOG1":
        #    self._simgGraph.nodes[state_id]['log'] = state.curr_stmt.arg2_val
        # self._simgGraph.nodes[state_id]['csts'] = '\n'.join([str(x.dump()) for x in state.constraints])
        self.timestamp += 1
        return state_id

    def _add_edge(self, new_state_id, parent_state_id):
        """
        Add an edge to the graph.
        """
        self._simgGraph.add_edge(new_state_id, parent_state_id)

    def _dump_graph(self):
        """
        Dump the graph to a .dot file.
        The dumped graph is located in the /tmp/ directory and its name is printed in the log.
        """
        output_filename = tempfile.NamedTemporaryFile(prefix="greed_simgrviz_", suffix=".dot", delete=False).name
        log.info(f"Dumping simgrviz .dot output to file {output_filename}")

        s = 'digraph g {\n'
        s += '\tnode[fontname="courier"];\n'
        for node_id in self._simgGraph.nodes:
            node = self._simgGraph.nodes[node_id]

            shape = 'box'
            s += '\t\"{}\" [shape={},label='.format(node_id[:10], shape)
            s += '<ts:{}<br align="left"/>'.format(node["timestamp"])
            s += '<br align="left"/>pc:{}'.format(node["pc"])
            if node.get("log", None):
                s += '<br align="left"/>log:{}'.format(node["log"])
            # s += '<br align="left"/>csts:{}'.format(node["csts"])
            s += '<br align="left"/>>];\n'

        s += '\n'

        for edge in self._simgGraph.edges:
            start = edge[0][:10]
            end = edge[1][:10]
            s += '\t\"%s\" -> \"%s\";\n' % (end, start)

        s += '}'

        with open(output_filename, "w") as simgrviz_file:
            simgrviz_file.write(s)