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
