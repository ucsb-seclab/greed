import networkx as nx
from typing import List

from greed.TAC import TAC_Statement


class Block(object):
    """
    A TAC Basic Block.
    """
    def __init__(self, statements: List[TAC_Statement], block_id: str):
        """
        Args:
            statements: List of TAC statements
            block_id: Block id
        """
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

        self._subgraph = None
        self._acyclic_subgraph = None

    @property
    def succ(self):
        """
        Returns: 
            List of successors blocks
        """
        if self._succ is None:
            self._succ = list(self.cfg.graph.successors(self))
        return self._succ

    @property
    def pred(self):
        """
        Returns: 
            List of predecessors blocks
        """
        if self._pred is None:
            self._pred = list(self.cfg.graph.predecessors(self))
        return self._pred

    @property
    def ancestors(self):
        """
        Returns: 
            List of ancestors blocks
        """
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
        """
        Returns: 
            List of descendants blocks
        """
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
    def subgraph(self):
        """
        Returns: 
            Subgraph with this basic block as the root node (with cycles)
        """
        if self._subgraph is None:
            self._subgraph = nx.dfs_tree(self.cfg.graph, source=self)
            for node in self._subgraph.nodes():
                for succ in node.succ:
                    if not self._subgraph.has_edge(node, succ):
                        self._subgraph.add_edge(node, succ)

        return self._subgraph

    @property
    def acyclic_subgraph(self):
        """
        Returns: 
            Subgraph with this basic block as the root node (without cycles)
        """
        if self._acyclic_subgraph is None:
            self._acyclic_subgraph = nx.dfs_tree(self.cfg.graph, source=self)

        return self._acyclic_subgraph

    def __str__(self):
        return "Block at {}".format(self.id)

    def __repr__(self):
        return str(self)
