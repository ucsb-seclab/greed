
import logging 

log = logging.getLogger(__name__)

def collect_preds(target_block, b_slice, score):
    preds = target_block.pred
    for p in preds:
        import ipdb; ipdb.set_trace()
        if p.id not in [x[0].id for x in b_slice]:
            #log.debug(f"Adding pred {p} with score {score}")
            b_slice.append((p,score))
            score = score+1
            return collect_preds(p, b_slice, score)
    return score

def run_backward_slice(project, source_block, target_block):

    # A collection of backward slices 
    b_slices = []
    # bslice is a list of tuple (block_id, distance_to_target_block)
    b_slice = []
    # Distance from target_block
    score = 1

    #log.debug(f"Building slice starting from {source_block.id} to {target_block.id}")
    
    def _run_backward_slice(source_block, target_block, b_slice, score):
        last_score = collect_preds(target_block, b_slice, score)
        blocks = [x[0].id for x in b_slice]
        if source_block.id in blocks:
            #log.debug(f"Found a slice")
            b_slices.append(b_slice)
        else:
            # Get Xrefs
            all_xrefs = []
            curr_func = target_block.function
            for func_id, func_obj in project.function_at.items():
                if len(func_obj.callprivate_target_sources[curr_func.id]) != 0:
                    all_xrefs.append(func_obj.callprivate_target_sources[curr_func.id])
            for xrefs in all_xrefs:
                for xref in xrefs:
                    #log.debug(f"xref at {xref}")
                    _run_backward_slice(source_block, project.factory.block(xref), list(b_slice), last_score)

    _run_backward_slice(source_block, target_block, b_slice, score)

    return b_slices
