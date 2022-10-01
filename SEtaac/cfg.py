import logging
from typing import List

import networkx as nx

log = logging.getLogger(__name__)


class CFG(object):
    def __init__(self):

        self.graph = nx.DiGraph()

        # keep basic block organized in a dictionary
        self.bbs = list()
        self._bb_at = dict()
        self._dominators = None

        self.root = None

    def filter_stmt(self, names: List[str]):
        if isinstance(names, str):
            names = [names]
        return [stmt for bb in self.bbs for stmt in bb.statements if stmt.__internal_name__ in names]

    @property
    def dominators(self):
        if not self._dominators:
            self._dominators = {k: v for k, v in nx.immediate_dominators(self.graph, 0).items()}
        return self._dominators

    def dump(self, filename):
        log.info(f"Dumping cfg .dot output to file {filename}")

        dot = "digraph g {\n"
        dot += "splines=ortho;\n"
        dot += "node[fontname=\"courier\"];\n"
        
        for block_id, block in self._bb_at.items():
            revert_block = False
            color = "black"

            label = []
            label.append(f"block_addr: {block_id}")

            for stmt in block.statements:
                stmt_str = ""

                for res_var in stmt.res_vars:
                    stmt_str += f"{res_var}"

                    if stmt.res_vals.get(res_var,None):
                        stmt_str += f"({hex(stmt.res_vals[res_var].value)})"
                    stmt_str += " "
                # Finishing parsing results 
                stmt_str += "= "
                
                # Add opcode
                stmt_str += f"{stmt.__internal_name__} "
                
                # Add args
                for arg_var in stmt.arg_vars:
                    stmt_str += f"{arg_var}"

                    if stmt.arg_vals.get(arg_var,None):
                        stmt_str += f"({hex(stmt.arg_vals[arg_var].value)})"
                    stmt_str += " "

                label.append(f"{stmt.id}: {stmt_str}")
                if "REVERT" in stmt.__internal_name__:
                    color = "red"
                if "CALLDATA" in stmt.__internal_name__:
                    color = "orange"

            label = "\n".join(label)
            dot += f"\"{block_id}\" [shape=box, color={color}, \nlabel=\"{label}\"];\n\n"

        dot += "\n"

        for a, b in self.graph.edges:
            dot += f"\"{a.id}\" -> \"{b.id}\";\n"

        dot += "}"

        with open(filename, "w") as dump_file:
            dump_file.write(dot)
