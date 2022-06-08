class ExternalData(Exception):
    pass


class SymbolicError(Exception):
    pass


class IntractablePath(Exception):
    def __init__(self, trace):
        self.trace = tuple(trace)


class VMException(Exception):
    pass
