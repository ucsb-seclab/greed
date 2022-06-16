class TACparser_NO_OPS(Exception):
    pass

class VMException(Exception):
    pass

class VM_NoSuccessors(VMException):
    pass

class VM_UnexpectedSuccessors(VMException):
    pass

class SymbolicError(VMException):
    pass

class ExternalData(VMException):
    pass

class IntractablePath(VMException):
    def __init__(self, trace):
        self.trace = tuple(trace)
