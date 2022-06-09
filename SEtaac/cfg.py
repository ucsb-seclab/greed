import logging

import networkx as nx


class BB(object):
    def __init__(self, ins):
        self.ins = ins

        self.cfg = None

        self.start = self.ins[0].addr
        self.succ_addrs = set()

        self.branch = self.ins[-1].op == 0x57
        self.indirect_jump = self.ins[-1].op in (0x56, 0x57)

        # cached properties
        self._succ = None
        self._pred = None
        self._ancestors = None
        self._descendants = None

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
                if self.cfg.graph.has_edge(self.cfg._bb_at[self.start], self.cfg._bb_at[bb.start]):
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
        return f'BB @ {self.start}'

    def __repr__(self):
        return str(self)


class CFG(object):
    def __init__(self, TAC_cfg_raw):

        self.graph = nx.DiGraph()
        # Data from Gigahorse in a dictionary
        self.TAC_cfg_raw = TAC_cfg_raw

        # keep basic block organized in a dictionary
        self._bb_at = dict()
        self.bbs = list()
        self._dominators = None

        # resolve basic blocks and edges
        self._import_cfg_gigahorse()
        
        '''
        self.trim()
        self.root = self._bb_at[0]
        self._ins_at = {i.addr: i for bb in self.bbs for i in bb.ins}
        self.shortest_paths = nx.single_source_shortest_path(self.graph, self.root)
        '''

    def filter_ins(self, names, reachable=False):
        if isinstance(names, str):
            names = [names]
        if not reachable:
            return [ins for bb in self.bbs for ins in bb.ins if ins.name in names]
        else:
            return [ins for bb in self.bbs for ins in bb.ins if ins.name in names and 0 in bb.ancestors | {bb.start}]

    def _import_cfg_gigahorse(self):
        # TODO
        # here parse the TAC_cfg_raw 
        import ipdb; ipdb.set_trace()
        pass

    @property
    def dominators(self):
        if not self._dominators:
            self._dominators = {k: v for k, v in nx.immediate_dominators(self.graph, 0).items()}
        return self._dominators

    def trim(self):
        keep = set(nx.descendants(self.graph, self.root)) | {self.root}
        delete = set(self.bbs) - keep
        self.bbs = [bb for bb in self.bbs if bb in keep]
        logging.info(f'Trimming CFG (deleting {[hex(bb.start)[2:] for bb in delete]})')
        for bb in delete:
            del self._bb_at[bb.start]
            self.graph.remove_node(bb)
