import networkx as nx

from SEtaac.TAC.gigahorse_ops import TAC_Nop


class TAC_Block(object):
    def __init__(self, statements, block_id):
        # WARNING: assuming BB indexes are UNIQUE.
        self.id = block_id
        self.statements = statements

        # keep a dictionary from statement id to statement
        self._statement_at = {s.id: s for s in self.statements}
        self.first_ins = self.statements[0]

        self.cfg = None
        self.function = None

        self.fallthrough_edge = None

        # cached properties
        self._succ = None
        self._pred = None
        self._ancestors = None
        self._descendants = None

        self._shortest_paths = None

        self._acyclic_subgraph = None

    @property
    def succ(self):
        if self._succ is None:
            self._succ = list(self.cfg.graph.successors(self))
        return self._succ

    @property
    def pred(self):
        if self._pred is None:
            self._pred = list(self.cfg.graph.predecessors(self))
        return self._pred

    @property
    def ancestors(self):
        if self._ancestors is None:
            reversed_subtree = nx.dfs_tree(self.cfg.graph.reverse(), source=self)
            self._ancestors = list(set(reversed_subtree) - {self})
            # if there is a loop, add the current bb to it's ancestors
            for bb in self._ancestors:
                if self.cfg.graph.has_edge(self, bb):
                    self._ancestors += [self]
                    break
        return self._ancestors

    @property
    def descendants(self):
        if self._descendants is None:
            subtree = nx.dfs_tree(self.cfg.graph, source=self)
            self._descendants = list(set(subtree) - {self})

            # if there is a loop, add the current bb to it's descendants
            for bb in self._descendants:
                if self.cfg.graph.has_edge(bb, self):
                    self._descendants += [self]
                    break

        return self._descendants

    @property
    def shortest_paths(self):
        if self._shortest_paths is None:
            self._shortest_paths = nx.single_source_shortest_path(self.graph, self.root)
        return self._shortest_paths

    @property
    def acyclic_subgraph(self):
        if self._acyclic_subgraph is None:
            self._acyclic_subgraph = nx.dfs_tree(self.cfg.graph, source=self)

        return self._acyclic_subgraph

    @property
    def subgraph(self):
        if self._acyclic_subgraph is None:
            self._acyclic_subgraph = nx.dfs_tree(self.cfg.graph, source=self)
            for node in self._acyclic_subgraph.nodes():
                for succ in node.succ:
                    if not self._acyclic_subgraph.has_edge(node, succ):
                        self._acyclic_subgraph.add_edge(node, succ)

        return self._acyclic_subgraph

    def __str__(self):
        return "Block at {}".format(self.id)

    def __repr__(self):
        return str(self)


class CFG(object):
    def __init__(self):

        self.graph = nx.DiGraph()

        # keep basic block organized in a dictionary
        self.bbs = list()
        self._bb_at = dict()
        self._dominators = None

    def filter_stmt(self, names):
        if isinstance(names, str):
            names = [names]
        return [stmt for bb in self.bbs for stmt in bb.statements if stmt.__internal_name__ in names]

    @property
    def dominators(self):
        if not self._dominators:
            self._dominators = {k: v for k, v in nx.immediate_dominators(self.graph, 0).items()}
        return self._dominators
