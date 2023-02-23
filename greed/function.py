
import logging
import networkx as nx

from collections import defaultdict
from typing import List, Mapping

from greed.block import Block
from greed.cfg import CFG
from greed.factory import Factory
from greed.solver.shortcuts import *

log = logging.getLogger(__name__)

# id: block id at wich the function start
# signature: four bytes signature of the function
# name: full prototype of the function if retrieved by Gigahorse
# public: wether the function is public or not
# blocks: list of blocks belonging to this function
# arguments: TAC names of the arguments of this function
class TAC_Function:
    def __init__(self, id: str, signature: str, name: str, public: bool, blocks: List[Block], arguments: List[str]):
        self.id = id
        self.signature = signature
        self.name = name
        self.public = public
        self.blocks = blocks
        self.arguments = arguments

        # populate source -> target map
        self.callprivate_source_target = self._get_callprivate_source_target()
        # populate target -> source map
        self.callprivate_target_sources = defaultdict(list)
        for source, target in self.callprivate_source_target.items():
            self.callprivate_target_sources[target].append(source)

        self.returnprivate_block_ids = [stmt.block_id
                                        for bb in self.blocks
                                        for stmt in bb.statements
                                        if stmt.__internal_name__ == "RETURNPRIVATE"]

        self.cfg = None
        self.usedef_graph = nx.DiGraph()

    def _get_callprivate_source_target(self) -> Mapping[str, str]:
        call_targets = dict()
        for bb in self.blocks:
            for stmt in bb.statements:
                if stmt.__internal_name__ == "CALLPRIVATE":
                    target_bb_id = hex(bv_unsigned_value(stmt.arg1_val))
                    call_targets[stmt.block_id] = target_bb_id
        return call_targets

    # Building the intra-functional CFG of a target function.
    def build_cfg(self, factory: Factory, tac_block_succ: Mapping[str, List[str]]):
        cfg = CFG()
        for bb in self.blocks:
            bb.cfg = cfg
            cfg.graph.add_node(bb)

        for a in self.blocks:
            # Adding information about successors from Gigahorse analysis
            for b_id in tac_block_succ.get(a.id, []):
                cfg.graph.add_edge(a, factory.block(b_id))

        cfg.bbs = list(cfg.graph.nodes())
        cfg._bb_at = {bb.id: bb for bb in cfg.bbs}

        cfg.root = factory.block(self.id)

        return cfg
    
    def build_use_def_graph(self):
        for bb in self.blocks:
            for stmt in bb.statements:
                # Declare the statement node 
                self.usedef_graph.add_node(stmt.id, type="stmt", stmt_name=stmt.__internal_name__, block_id=stmt.block_id)
                
                # Uses are the arguments of the statement
                use_index = 0
                for arg in stmt.arg_vars:
                    # add the argument as node if it is not there yet
                    if arg not in self.usedef_graph.nodes:
                        # Check if there is a value 
                        if stmt.arg_vals.get(arg, None):
                            self.usedef_graph.add_node(arg, type="var", value=hex(stmt.arg_vals[arg].value))
                        else:
                            self.usedef_graph.add_node(arg, type="var", value='')

                    # add the edge between the argument and the statement
                    self.usedef_graph.add_edge(arg,stmt.id, index=use_index, type='use')
                    use_index+=1
                
                # Defs are the return values of the statement
                def_index = 0
                for ret in stmt.res_vars:
                    # add the argument as node if it is not there yet
                    if ret not in self.usedef_graph.nodes:
                        # add the return value as node 
                        # Check if there is a value 
                        if stmt.res_vals.get(ret, None):
                            self.usedef_graph.add_node(ret, type="var", value=hex(stmt.res_vals[ret].value))
                        else:
                            self.usedef_graph.add_node(ret, type="var", value='')

                    # add the edge between the def and the statement
                    self.usedef_graph.add_edge(stmt.id, ret, index=def_index, type='def')
                    def_index+=1

    
    def dump_use_def_graph(self,filename):
        log.info(f"Dumping usedef .dot output to file {filename}")

        dot = "digraph g {\n"
        dot += "splines=ortho;\n"
        dot += "node[fontname=\"courier\"];\n"

        # Iterate though the nodes in the graph
        for node in self.usedef_graph.nodes:
            label = []
            # Get the node attributes
            node_attr = self.usedef_graph.nodes[node]

            if node_attr["type"] == "stmt":
                label.append(f"id: {node}")
                label.append(f"stmt_name: {node_attr['stmt_name']}")
                label.append(f"block_id: {node_attr['block_id']}")
                label = "\n".join(label)
            else:
                label.append(f"var: {node}")
                label.append(f"value: {node_attr['value']}")
                label = "\n".join(label)

            dot += f"\"{node}\" [shape=box, color=black, \nlabel=\"{label}\"];\n\n"

        dot += "\n"

        for a, b in self.usedef_graph.edges:
            elabel = []
            # Get the edge attributes
            edge_attr = self.usedef_graph.edges[a, b]
            if edge_attr["type"] == "use":
                elabel.append(f'used_{edge_attr.get("index")}')
                elabel = "\n".join(elabel)
                dot += f"\"{a}\" -> \"{b}\" [color=blue, \nlabel=\"{elabel}\"];\n"
            else:
                elabel.append(f'def_{edge_attr.get("index")}')
                elabel = "\n".join(elabel)
                dot += f"\"{a}\" -> \"{b}\" [color=green, \nlabel=\"{elabel}\"];\n"

        dot += "}"

        with open(filename, "w") as dump_file:
            dump_file.write(dot)
    

