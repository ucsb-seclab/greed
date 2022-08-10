
from SEtaac.state_plugins import SimStatePlugin
from SEtaac.utils.solver.shortcuts import *


class LambdaTaint:
    def __init__(self):
        return
    def instantiate(self, curr_taint_check):
        return []

class LambdaTaintRange(LambdaTaint):
    def __init__(self, state, start, size, next):
        super(LambdaTaintRange, self).__init__()
        self.start = start
        self.size
        self.state = state

        self.next = None

    def instantiate(self, read_index, curr_taint_check=None):
        
        taint_check = If(And(BV_ULE(self.start, read_index), BV_ULT(read_index, BV_Add(self.start, self.size))),
                                Equal(self.state.tainted_reads[read_index], BVV(1,1)),
                                Equal(self.state.tainted_reads[read_index], BVV(0,1))) 

        self.next.instantiate(taint_check)

        return instance

class LambdaTaintOverlappingRanges(LambdaTaint):
    def __init__(self, state, r1start, r1size, r2start, r2size, next):
        super(LambdaTaintOverlappingRanges, self).__init__()
        self.r1start = r1start
        self.r1size = r1size
        self.r2start = r2start
        self.r2size = r2size
        self.state = state

        self.next = None

    def instantiate(self, read_index, curr_taint_check=None):
        
        self.r1end = BV_ADD(self.r1start + self.r1size)
        self.r2end = BV_ADD(self.r2start + self.r2size)
        
        taint_check = If(Or( And( BV_UGE(self.r2start, self.r1start), BV_ULE(self.r2start, self.r1end)), 
                             And( BV_UGE(self.r2end, self.r1start), BV_ULE(self.r2end, self.r1end)),
                             And( )

        self.next.instantiate(taint_check)

        return instance

class LambdaTaintStore(LambdaTaint):
    def __init__(self, state, store, next):
        self.state = state
        self.store = store

        self.next = None
    
    def instantiate(self, read_index, curr_taint_check):
        import ipdb; ipdb.set_trace()
        '''
        # This if is completely broken, FIXME
        if self.store.value.is_register()
            # If the value the store moved at the index is tainted, and the read is reading from that index,
            # then this will set the variable to tainted.
            # This is also broken, FIXME
            my_check = And( Equal(read_index, store.index), Equal(self.state.tainted_registers[self.store.value], BVV(1,0)))

            if self.next is None:
                return [my_check]
            else:
                assert(False)
        else:
            assert(False)
        '''

class SimStateTaints(SimStatePlugin):
    def __init__(self):
        super(SimStateTaints, self).__init__()
        self.lambda_taints = None 
        self.tainted_reads = dict()
        self.tainted_registers = dict()
        self.taint_constraints = set()

        self.taints = {}
    
    def set_calldata_taint(self, start=0, size=-1):
        self.taints["CALLDATACOPY"] = (start,size)
        '''
        if size != -1:
            taint = LambdaTaintRange(self.state, start, size, LambdaTaint())
            self.lambda_taints = taint
        else:
            assert(False)
        '''
    
    def add_taint_range(self,)
    
    def is_read_tainted(self, read_index):
        assert(is_concrete(read_index)), "As of now support only concrete offset"
        self.taint_constraints.add(self.lambda_taints.instantiate(read_index))
    
    def copy(self):
        return self(**self.__dict__)