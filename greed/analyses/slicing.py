import itertools
import networkx as nx


# NOTE: all this stuff is approximate, we should either 1. move it somewhere else outside of greed or 2. make it precise/guaranteed


def inline_cfg(p, cfg, max_rounds=10):
    """
    Inline max_depth levels of callprivates in the cfg, only when there is a single path in the callprivate
    """
    # TODO: inline callprivate in type analysis, e.g., 0x36ff0C3C161dE6F664B4fcA9149942e733F50eC7 is wrong

    if max_rounds == 0:
        return cfg
    
    new_cfg = None
    for callprivate in [n for n in cfg.nodes if n.__internal_name__ == "CALLPRIVATE"]:
        callprivate_target_function = p.factory.block(hex(callprivate.arg1_val.value)).function
        callprivate_cfg = callprivate_target_function.cfg.stmt_cfg

        # skip if not a single path
        if max([len(list(callprivate_cfg.successors(s))) for s in callprivate_cfg.nodes] or [0xff,]) > 1:
            continue

        callprivate_path = list(nx.topological_sort(callprivate_cfg))
        if callprivate_path[-1].__internal_name__ != "RETURNPRIVATE":
            # skip if no returnprivate
            continue

        # skip if returnprivate does not return exactly the number of vars expected
        returnprivate_args = callprivate_path[-1].arg_vars[1:]
        callprivate_ress = callprivate.res_vars
        if len(callprivate_ress) != len(returnprivate_args):
            continue

        # read arg-alias map
        callprivate_args = callprivate.arg_vars[1:]
        args_alias = callprivate_target_function.arguments
        if len(callprivate_args) != len(args_alias):
            # skip if invalid args
            continue
        alias_arg_map = dict(zip(args_alias, callprivate_args))

        # skip if returnprivate returns one or more of the args without any processing
        if any([a in returnprivate_args for a in args_alias]):
            continue

        # alias the return variable
        alias_arg_map.update(dict(zip(returnprivate_args, callprivate_ress)))
            
        # pop CALLPRIVATEARGS
        while callprivate_path[0].__internal_name__ == "CALLPRIVATEARG":
            callprivate_path.pop(0)

        # pop RETURNPRIVATE
        callprivate_path.pop(-1)

        # init new cfg if not done yet
        new_cfg = new_cfg or nx.DiGraph()
        new_cfg.add_nodes_from(cfg.nodes)
        new_cfg.add_edges_from(cfg.edges)

        inline_predecessors = list(cfg.predecessors(callprivate))
        inline_successors = list(cfg.successors(callprivate))

        # remove the callprivate node
        new_cfg.remove_node(callprivate)

        for _s in callprivate_path:
            s = _s.copy(alias_arg_map)

            for pred in inline_predecessors:
                new_cfg.add_edge(pred, s)
            inline_predecessors = [s, ]

        for pred in inline_predecessors:
            for succ in inline_successors:
                new_cfg.add_edge(pred, succ)
                
        # print(list(nx.topological_sort(cfg)))
        # print(list(nx.topological_sort(new_cfg)))
        # import IPython; IPython.embed(); exit()

    return inline_cfg(p, new_cfg or cfg, max_rounds=max_rounds-1)


def _backward_slice_instructions(p, target_stmt, target_function, target_function_stmt_cfg, target_vars=None, thin_slice=True):
    """
    Backward slice algorithm from https://www.math.arizona.edu/~glickenstein/math443f08/coogan.pdf
    """
    target_vars = target_vars or target_stmt.arg_vars
    assert all([v in target_stmt.arg_vars for v in target_vars])

    queue = {target_stmt, }
    relevant_map = {stmt_id: set() for stmt_id in p.statement_at}
    relevant_map[target_stmt.id] = set(target_vars)
    # fixpoint for each edge i-j in the cfg
    while queue:
        curr = queue.pop()

        for pred in target_function_stmt_cfg.predecessors(curr):
            for var in relevant_map[curr.id]:
                # if i does not define a relevant variable var of j, add var to i’s relevant variables
                if var not in pred.res_vars and var not in relevant_map[pred.id]:
                    relevant_map[pred.id].add(var)
                    # if anything is updated, queue pred until fixpoint
                    queue.add(pred)
                # if i does define relevant variable var of j, add variables referenced by i to i’s relevant variables
                elif var in pred.res_vars:
                    for var2 in pred.arg_vars:
                        if var2 not in relevant_map[pred.id]:
                            relevant_map[pred.id].add(var2)
                            # if anything is updated, queue pred until fixpoint
                            queue.add(pred)

    slice = {target_stmt, }
    # for each edge i-j in the cfg
    for stmt_a, stmt_b in target_function_stmt_cfg.edges():
        # if i defines a relevant variable of j, add i to slice
        for var in relevant_map[stmt_b.id]:
            if var in stmt_a.res_vars:
                slice.add(stmt_a)

    if thin_slice is False:
        raise Exception("Only thin slice supported for now")

    return slice


def _forward_slice_instructions(p, target_stmt, target_function, target_function_stmt_cfg, target_vars=None, thin_slice=True):
    """
    Forward slice algorithm (pretty much like the backward slice)
    """
    target_vars = target_vars or target_stmt.res_vars
    assert all([v in target_stmt.res_vars for v in target_vars])

    queue = {target_stmt, }
    relevant_map = {stmt_id: set() for stmt_id in p.statement_at}
    relevant_map[target_stmt.id] = set(target_vars)
    # fixpoint for each edge i-j in the cfg
    while queue:
        curr = queue.pop()

        for succ in target_function_stmt_cfg.successors(curr):
            for var in relevant_map[curr.id]:
                # add any relevant var of i to j's relevant vars
                if var not in relevant_map[succ.id]:
                    relevant_map[succ.id].add(var)
                    # if anything is updated, queue succ until fixpoint
                    queue.add(succ)

                # if j uses a relevant variable var of i, add j's defines to j's relevant variables
                if var in succ.arg_vars:
                    for var2 in succ.res_vars:
                        if var2 not in relevant_map[succ.id]:
                            relevant_map[succ.id].add(var2)
                            # if anything is updated, queue succ until fixpoint
                            queue.add(succ)

    slice = {target_stmt, }
    # for each edge i-j in the cfg
    for stmt_a, stmt_b in target_function_stmt_cfg.edges():
        # if j uses a relevant variable of i, add j to slice
        for var in relevant_map[stmt_a.id]:
            if var in stmt_b.arg_vars:
                slice.add(stmt_b)

    if thin_slice is False:
        raise Exception("Only thin slice supported for now")

    return slice


def _bidirectional_slice_instructions(p, target_stmt, target_function, target_function_stmt_cfg, target_vars, thin_slice=True):
    """
    Forward+Backward slice algorithm
    """
    _forward_slice = _forward_slice_instructions(p, target_stmt, target_function, target_function_stmt_cfg, target_vars, thin_slice)
    _backward_slice = _backward_slice_instructions(p, target_stmt, target_function, target_function_stmt_cfg, target_vars, thin_slice)

    return _forward_slice | _backward_slice


def _slice(slicing_alg, p, target_addr, target_vars, thin_slice=True):
    target_stmt = p.factory.statement(target_addr)
    target_block = p.factory.block(target_stmt.block_id)
    target_function = target_block.function

    target_function_stmt_cfg = inline_cfg(p, target_function.cfg.stmt_cfg)
    slice = slicing_alg(p, target_stmt, target_function, target_function_stmt_cfg, target_vars, thin_slice)

    slice_graph = target_function_stmt_cfg.copy()

    nodes_to_delete = set(slice_graph.nodes()) - slice
    for node in nodes_to_delete:
        slice_graph.add_edges_from(
            itertools.product(
                slice_graph.predecessors(node),
                slice_graph.successors(node)
            )
        )
        slice_graph.remove_node(node)

    return slice_graph


def backward_slice(p, target_addr, target_vars=None, thin_slice=True):
    return _slice(_backward_slice_instructions, p, target_addr, target_vars, thin_slice)


def forward_slice(p, target_addr, target_vars=None, thin_slice=True):
    return _slice(_forward_slice_instructions, p, target_addr, target_vars, thin_slice)


def bidirectional_slice(p, target_addr, target_vars=None, thin_slice=True):
    return _slice(_bidirectional_slice_instructions, p, target_addr, target_vars, thin_slice)
