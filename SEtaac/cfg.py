import networkx as nx
from typing import List


class CFG(object):
    def __init__(self):

        self.graph = nx.DiGraph()

        # keep basic block organized in a dictionary
        self.bbs = list()
        self._bb_at = dict()
        self._dominators = None

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
        dot = "digraph g {\n"
        dot += "splines=ortho;\n"
        dot += "node[fontname=\"courier\"];\n"
        
        for block_id, block in self._bb_at.items():
            revert_block = False
            color = "black"

            label = []
            label.append(f"block_addr: {block_id}")

            for stmt in block.statements:
                label.append(f"{stmt.id}: {stmt}")
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
