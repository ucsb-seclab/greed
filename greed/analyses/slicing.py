import itertools


def _backward_slice_instructions(target_stmt, target_function, target_vars=None, thin_slice=True):
    """
    Backward slice algorithm from https://www.math.arizona.edu/~glickenstein/math443f08/coogan.pdf
    """
    target_vars = target_vars or target_stmt.arg_vars
    assert all([v in target_stmt.arg_vars for v in target_vars])

    queue = {target_stmt, }
    relevant_map = {stmt.id: set() for block in target_function.blocks for stmt in block.statements}
    relevant_map[target_stmt.id] = set(target_vars)
    # fixpoint for each edge i-j in the cfg
    while queue:
        curr = queue.pop()

        for pred in target_function.cfg.stmt_cfg.predecessors(curr):
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
    for stmt_a, stmt_b in target_function.cfg.stmt_cfg.edges():
        # if i defines a relevant variable of j, add i to slice
        for var in relevant_map[stmt_b.id]:
            if var in stmt_a.res_vars:
                slice.add(stmt_a)

    if thin_slice is False:
        raise Exception("Only thin slice supported for now")

    return slice


def _forward_slice_instructions(target_stmt, target_function, target_vars=None, thin_slice=True):
    """
    Forward slice algorithm (pretty much like the backward slice)
    """
    target_vars = target_vars or target_stmt.res_vars
    assert all([v in target_stmt.res_vars for v in target_vars])

    queue = {target_stmt, }
    relevant_map = {stmt.id: set() for block in target_function.blocks for stmt in block.statements}
    relevant_map[target_stmt.id] = set(target_vars)
    # fixpoint for each edge i-j in the cfg
    while queue:
        curr = queue.pop()

        for succ in target_function.cfg.stmt_cfg.successors(curr):
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
    for stmt_a, stmt_b in target_function.cfg.stmt_cfg.edges():
        # if j uses a relevant variable of i, add j to slice
        for var in relevant_map[stmt_a.id]:
            if var in stmt_b.arg_vars:
                slice.add(stmt_b)

    if thin_slice is False:
        raise Exception("Only thin slice supported for now")

    return slice


def _bidirectional_slice_instructions(target_stmt, target_function, target_vars, thin_slice=True):
    """
    Forward+Backward slice algorithm
    """
    _forward_slice = _forward_slice_instructions(target_stmt, target_function, target_vars, thin_slice)
    _backward_slice = _backward_slice_instructions(target_stmt, target_function, target_vars, thin_slice)

    return _forward_slice | _backward_slice


def _slice(slicing_alg, p, target_addr, target_vars, thin_slice=True):
    target_stmt = p.factory.statement(target_addr)
    target_block = p.factory.block(target_stmt.block_id)
    target_function = target_block.function

    slice = slicing_alg(target_stmt, target_function, target_vars, thin_slice)

    slice_graph = target_function.cfg.stmt_cfg.copy()

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
