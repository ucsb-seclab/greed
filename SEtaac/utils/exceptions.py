class VMException(Exception):
    pass


class VMNoSuccessors(VMException):
    pass


class VMUnexpectedSuccessors(VMException):
    pass


class VMSymbolicError(VMException):
    pass


class VMExternalData(VMException):
    pass

class GreedException(Exception):
    pass
