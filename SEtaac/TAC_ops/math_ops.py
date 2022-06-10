

__all__ = [
           'TAC_Add', 'TAC_Sub', 'TAC_Mul', 'TAC_Div', 'TAC_Sdiv',
           'TAC_Mod', 'TAC_Smod','TAC_Addmod','TAC_Mulmod', 'TAC_Exp',
           'TAC_Signextend', 'TAC_Lt', 'TAC_Gt', 'TAC_Slt', 'TAC_Sgt', 
           'TAC_Eq', 'TAC_Iszero', 'TAC_And', 'TAC_Or', 'TAC_Xor',
           'TAC_Not', 'TAC_Byte', 'TAC_Shl', 'TAC_Shr', 'TAC_Sar'
           ]

class TAC_Add:
    __internal_name__ = "ADD"
    def __init__(self):
        self.op1_var = None
        self.op2_var = None
        self.res_var = None
        
        self.op1_val = None
        self.op2_val = None
        self.res_val = None

    def parse(self, raw_stmt):
        self.op1_var = raw_stmt.operands[0]
        self.op2_var = raw_stmt.operands[1]
        self.res_var = raw_stmt.defs[0]
        
        self.op1_val = raw_stmt.values.get(self.op1_var, None)
        self.op2_val = raw_stmt.values.get(self.op2_var, None)
        self.res_val = raw_stmt.values.get(self.res_var, None)

    def handle(self, state):
        succ = state.copy()
        succ.registers[self.res] = succ.registers[self.op1_var] + succ.registers[self.op2_var]
        succ.pc = succ.next_statement()
        return [succ]

    def __str__(self):
        op1 = self.op1_var if not self.op1_val else self.op1_var + '({})'.format(self.op1_val)
        op2 = self.op2_var if not self.op2_val else self.op2_var + '({})'.format(self.op2_val)
        res = self.res_var if not self.res_val else self.res_var + '({})'.format(self.res_val)
        return "{} = {} + {}".format(res, op1,op2)

class TAC_Sub:
    __internal_name__ = "SUB"
    def __init__(self):
        self.op1_var = None
        self.op2_var = None
        self.res_var = None
        
        self.op1_val = None
        self.op2_val = None
        self.res_val = None

    def parse(self, raw_stmt):
        self.op1_var = raw_stmt.operands[0]
        self.op2_var = raw_stmt.operands[1]
        self.res_var = raw_stmt.defs[0]
        
        self.op1_val = raw_stmt.values.get(self.op1_var, None)
        self.op2_val = raw_stmt.values.get(self.op2_var, None)
        self.res_val = raw_stmt.values.get(self.res_var, None) 
    
    def handle(self, state):
        pass

    def __str__(self):
        op1 = self.op1_var if not self.op1_val else self.op1_var + '({})'.format(self.op1_val)
        op2 = self.op2_var if not self.op2_val else self.op2_var + '({})'.format(self.op2_val)
        res = self.res_var if not self.res_val else self.res_var + '({})'.format(self.res_val)
        return "{} = {} - {}".format(res, op1,op2)

class TAC_Mul:
    __internal_name__ = "MUL"
    def __init__(self):
        self.op1_var = None
        self.op2_var = None
        self.res_var = None
        
        self.op1_val = None
        self.op2_val = None
        self.res_val = None

    def parse(self, raw_stmt):
        self.op1_var = raw_stmt.operands[0]
        self.op2_var = raw_stmt.operands[1]
        self.res_var = raw_stmt.defs[0]
        
        self.op1_val = raw_stmt.values.get(self.op1_var, None)
        self.op2_val = raw_stmt.values.get(self.op2_var, None)
        self.res_val = raw_stmt.values.get(self.res_var, None)

    def handle(self, state):
        pass

    def __str__(self):
        op1 = self.op1_var if not self.op1_val else self.op1_var + '({})'.format(self.op1_val)
        op2 = self.op2_var if not self.op2_val else self.op2_var + '({})'.format(self.op2_val)
        res = self.res_var if not self.res_val else self.res_var + '({})'.format(self.res_val)
        return "{} = {} * {}".format(res, op1,op2)

class TAC_Div:
    __internal_name__ = "DIV"
    def __init__(self):
        self.op1_var = None
        self.op2_var = None
        self.res_var = None
        
        self.op1_val = None
        self.op2_val = None
        self.res_val = None

    def parse(self, raw_stmt):
        self.op1_var = raw_stmt.operands[0]
        self.op2_var = raw_stmt.operands[1]
        self.res_var = raw_stmt.defs[0]
        
        self.op1_val = raw_stmt.values.get(self.op1_var, None)
        self.op2_val = raw_stmt.values.get(self.op2_var, None)
        self.res_val = raw_stmt.values.get(self.res_var, None)

    def handle(self, state):
        pass

    def __str__(self):
        op1 = self.op1_var if not self.op1_val else self.op1_var + '({})'.format(self.op1_val)
        op2 = self.op2_var if not self.op2_val else self.op2_var + '({})'.format(self.op2_val)
        res = self.res_var if not self.res_val else self.res_var + '({})'.format(self.res_val)
        return "{} = {} / {}".format(res, op1,op2)

class TAC_Sdiv:
    __internal_name__ = "SDIV"
    def __init__(self):
        self.op1_var = None
        self.op2_var = None
        self.res_var = None
        
        self.op1_val = None
        self.op2_val = None
        self.res_val = None

    def parse(self, raw_stmt):
        self.op1_var = raw_stmt.operands[0]
        self.op2_var = raw_stmt.operands[1]
        self.res_var = raw_stmt.defs[0]
        
        self.op1_val = raw_stmt.values.get(self.op1_var, None)
        self.op2_val = raw_stmt.values.get(self.op2_var, None)
        self.res_val = raw_stmt.values.get(self.res_var, None)

    def handle(self, state):
        pass

    def __str__(self):
        op1 = self.op1_var if not self.op1_val else self.op1_var + '({})'.format(self.op1_val)
        op2 = self.op2_var if not self.op2_val else self.op2_var + '({})'.format(self.op2_val)
        res = self.res_var if not self.res_val else self.res_var + '({})'.format(self.res_val)
        return "{} = {} // {}".format(res, op1,op2)


class TAC_Mod:
    __internal_name__ = "MOD"
    def __init__(self):
        self.op1_var = None
        self.op2_var = None
        self.res_var = None
        
        self.op1_val = None
        self.op2_val = None
        self.res_val = None

    def parse(self, raw_stmt):
        self.op1_var = raw_stmt.operands[0]
        self.op2_var = raw_stmt.operands[1]
        self.res_var = raw_stmt.defs[0]
        
        self.op1_val = raw_stmt.values.get(self.op1_var, None)
        self.op2_val = raw_stmt.values.get(self.op2_var, None)
        self.res_val = raw_stmt.values.get(self.res_var, None)

    def handle(self, state):
        pass

    def __str__(self):
        op1 = self.op1_var if not self.op1_val else self.op1_var + '({})'.format(self.op1_val)
        op2 = self.op2_var if not self.op2_val else self.op2_var + '({})'.format(self.op2_val)
        res = self.res_var if not self.res_val else self.res_var + '({})'.format(self.res_val)
        return "{} = {} % {}".format(res, op1,op2)

class TAC_Smod:
    __internal_name__ = "SMOD"
    def __init__(self):
        self.op1_var = None
        self.op2_var = None
        self.res_var = None
        
        self.op1_val = None
        self.op2_val = None
        self.res_val = None

    def parse(self, raw_stmt):
        self.op1_var = raw_stmt.operands[0]
        self.op2_var = raw_stmt.operands[1]
        self.res_var = raw_stmt.defs[0]
        
        self.op1_val = raw_stmt.values.get(self.op1_var, None)
        self.op2_val = raw_stmt.values.get(self.op2_var, None)
        self.res_val = raw_stmt.values.get(self.res_var, None)

    def handle(self, state):
        pass

    def __str__(self):
        op1 = self.op1_var if not self.op1_val else self.op1_var + '({})'.format(self.op1_val)
        op2 = self.op2_var if not self.op2_val else self.op2_var + '({})'.format(self.op2_val)
        res = self.res_var if not self.res_val else self.res_var + '({})'.format(self.res_val)
        return "{} = {} /%/% {}".format(res, op1,op2)

class TAC_Addmod:
    __internal_name__ = "ADDMOD"
    def __init__(self):
        self.op1_var = None
        self.op2_var = None
        self.denominator_var = None
        self.res_var = None
        
        self.op1_val = None
        self.op2_val = None
        self.denominator_val = None
        self.res_val = None

    def parse(self, raw_stmt):
        self.op1_var = raw_stmt.operands[0]
        self.op2_var = raw_stmt.operands[1]
        self.denominator_var = raw_stmt.operands[2]
        self.res_var = raw_stmt.defs[0]
        
        self.op1_val = raw_stmt.values.get(self.op1_var, None)
        self.op2_val = raw_stmt.values.get(self.op2_var, None)
        self.denominator_val = raw_stmt.values.get(self.denominator_var, None)
        self.res_val = raw_stmt.values.get(self.res_var, None)

    def handle(self, state):
        pass

    def __str__(self):
        op1 = self.op1_var if not self.op1_val else self.op1_var + '({})'.format(self.op1_val)
        op2 = self.op2_var if not self.op2_val else self.op2_var + '({})'.format(self.op2_val)
        den = self.op2_var if not self.op2_val else self.op2_var + '({})'.format(self.op2_val)
        res = self.denominator_var if not self.denominator_val else self.denominator_var + '({})'.format(self.denominator_val)
        return "{} = ({} + {}) % {}".format(res, op1,op2, den)

class TAC_Mulmod:
    __internal_name__ = "MULMOD"
    def __init__(self):
        self.op1_var = None
        self.op2_var = None
        self.denominator_var = None
        self.res_var = None
        
        self.op1_val = None
        self.op2_val = None
        self.denominator_val = None
        self.res_val = None

    def parse(self, raw_stmt):
        self.op1_var = raw_stmt.operands[0]
        self.op2_var = raw_stmt.operands[1]
        self.denominator_var = raw_stmt.operands[2]
        self.res_var = raw_stmt.defs[0]
        
        self.op1_val = raw_stmt.values.get(self.op1_var, None)
        self.op2_val = raw_stmt.values.get(self.op2_var, None)
        self.denominator_val = raw_stmt.values.get(self.denominator_var, None)
        self.res_val = raw_stmt.values.get(self.res_var, None)

    def handle(self, state):
        pass

    def __str__(self):
        op1 = self.op1_var if not self.op1_val else self.op1_var + '({})'.format(self.op1_val)
        op2 = self.op2_var if not self.op2_val else self.op2_var + '({})'.format(self.op2_val)
        den = self.op2_var if not self.op2_val else self.op2_var + '({})'.format(self.op2_val)
        res = self.denominator_var if not self.denominator_val else self.denominator_var + '({})'.format(self.denominator_val)
        return "{} = ({} * {}) % {}".format(res, op1,op2, den)

class TAC_Exp:
    __internal_name__ = "EXP"
    def __init__(self):
        self.base_var = None
        self.exp_var = None
        self.res_var = None
        
        self.base_val = None
        self.exp_val = None
        self.res_val = None

    def parse(self, raw_stmt):
        self.base_var = raw_stmt.operands[0]
        self.exp_var = raw_stmt.operands[1]
        self.res_var = raw_stmt.defs[0]
        
        self.base_val = raw_stmt.values.get(self.base_var, None)
        self.exp_val = raw_stmt.values.get(self.exp_var, None)
        self.res_val = raw_stmt.values.get(self.res_var, None)

    def handle(self, state):
        pass

    def __str__(self):
        base = self.base_var if not self.base_val else self.base_var + '({})'.format(self.base_val)
        exp = self.exp_var if not self.exp_val else self.exp_var + '({})'.format(self.exp_val)
        res = self.res_var if not self.res_val else self.res_var + '({})'.format(self.res_val)
        return "{} = {} ^ {}".format(res, base, exp)

class TAC_Signextend:
    __internal_name__ = "SIGNEXTEND"
    def __init__(self):
        self.op1_var = None
        self.op2_var = None
        self.res_var = None
        
        self.op1_val = None
        self.op2_val = None
        self.res_val = None

    def parse(self, raw_stmt):
        self.op1_var = raw_stmt.operands[0]
        self.op2_var = raw_stmt.operands[1]
        self.res_var = raw_stmt.defs[0]
        
        self.op1_val = raw_stmt.values.get(self.op1_var, None)
        self.op2_val = raw_stmt.values.get(self.op2_var, None)
        self.res_val = raw_stmt.values.get(self.res_var, None)

    def handle(self, state):
        pass

    def __str__(self):
        op1 = self.op1_var if not self.op1_val else self.op1_var + '({})'.format(self.op1_val)
        op2 = self.op2_var if not self.op2_val else self.op2_var + '({})'.format(self.op2_val)
        res = self.res_var if not self.res_val else self.res_var + '({})'.format(self.res_val)
        return "{} = SIGNEXTEND {} {}".format(res, op1,op2)

class TAC_Lt:
    __internal_name__ = "LT"
    def __init__(self):
        self.op1_var = None
        self.op2_var = None
        self.res_var = None
        
        self.op1_val = None
        self.op2_val = None
        self.res_val = None

    def parse(self, raw_stmt):
        self.op1_var = raw_stmt.operands[0]
        self.op2_var = raw_stmt.operands[1]
        self.res_var = raw_stmt.defs[0]
        
        self.op1_val = raw_stmt.values.get(self.op1_var, None)
        self.op2_val = raw_stmt.values.get(self.op2_var, None)
        self.res_val = raw_stmt.values.get(self.res_var, None)

    def handle(self, state):
        pass

    def __str__(self):
        op1 = self.op1_var if not self.op1_val else self.op1_var + '({})'.format(self.op1_val)
        op2 = self.op2_var if not self.op2_val else self.op2_var + '({})'.format(self.op2_val)
        res = self.res_var if not self.res_val else self.res_var + '({})'.format(self.res_val)
        return "{} =  {} < {}".format(res, op1,op2)

class TAC_Gt:
    __internal_name__ = "GT"
    def __init__(self):
        self.op1_var = None
        self.op2_var = None
        self.res_var = None
        
        self.op1_val = None
        self.op2_val = None
        self.res_val = None

    def parse(self, raw_stmt):
        self.op1_var = raw_stmt.operands[0]
        self.op2_var = raw_stmt.operands[1]
        self.res_var = raw_stmt.defs[0]
        
        self.op1_val = raw_stmt.values.get(self.op1_var, None)
        self.op2_val = raw_stmt.values.get(self.op2_var, None)
        self.res_val = raw_stmt.values.get(self.res_var, None)

    def handle(self, state):
        pass

    def __str__(self):
        op1 = self.op1_var if not self.op1_val else self.op1_var + '({})'.format(self.op1_val)
        op2 = self.op2_var if not self.op2_val else self.op2_var + '({})'.format(self.op2_val)
        res = self.res_var if not self.res_val else self.res_var + '({})'.format(self.res_val)
        return "{} =  {} > {}".format(res, op1,op2)

class TAC_Slt:
    __internal_name__ = "SLT"
    def __init__(self):
        self.op1_var = None
        self.op2_var = None
        self.res_var = None
        
        self.op1_val = None
        self.op2_val = None
        self.res_val = None

    def parse(self, raw_stmt):
        self.op1_var = raw_stmt.operands[0]
        self.op2_var = raw_stmt.operands[1]
        self.res_var = raw_stmt.defs[0]
        
        self.op1_val = raw_stmt.values.get(self.op1_var, None)
        self.op2_val = raw_stmt.values.get(self.op2_var, None)
        self.res_val = raw_stmt.values.get(self.res_var, None)

    def handle(self, state):
        pass

    def __str__(self):
        op1 = self.op1_var if not self.op1_val else self.op1_var + '({})'.format(self.op1_val)
        op2 = self.op2_var if not self.op2_val else self.op2_var + '({})'.format(self.op2_val)
        res = self.res_var if not self.res_val else self.res_var + '({})'.format(self.res_val)
        return "{} =  {} (<) {}".format(res, op1,op2)


class TAC_Sgt:
    __internal_name__ = "SGT"
    def __init__(self):
        self.op1_var = None
        self.op2_var = None
        self.res_var = None
        
        self.op1_val = None
        self.op2_val = None
        self.res_val = None

    def parse(self, raw_stmt):
        self.op1_var = raw_stmt.operands[0]
        self.op2_var = raw_stmt.operands[1]
        self.res_var = raw_stmt.defs[0]
        
        self.op1_val = raw_stmt.values.get(self.op1_var, None)
        self.op2_val = raw_stmt.values.get(self.op2_var, None)
        self.res_val = raw_stmt.values.get(self.res_var, None)

    def handle(self, state):
        pass

    def __str__(self):
        op1 = self.op1_var if not self.op1_val else self.op1_var + '({})'.format(self.op1_val)
        op2 = self.op2_var if not self.op2_val else self.op2_var + '({})'.format(self.op2_val)
        res = self.res_var if not self.res_val else self.res_var + '({})'.format(self.res_val)
        return "{} =  {} (>) {}".format(res, op1,op2)

class TAC_Eq:
    __internal_name__ = "EQ"
    def __init__(self):
        self.op1_var = None
        self.op2_var = None
        self.res_var = None
        
        self.op1_val = None
        self.op2_val = None
        self.res_val = None

    def parse(self, raw_stmt):
        self.op1_var = raw_stmt.operands[0]
        self.op2_var = raw_stmt.operands[1]
        self.res_var = raw_stmt.defs[0]
        
        self.op1_val = raw_stmt.values.get(self.op1_var, None)
        self.op2_val = raw_stmt.values.get(self.op2_var, None)
        self.res_val = raw_stmt.values.get(self.res_var, None)

    def handle(self, state):
        pass

    def __str__(self):
        op1 = self.op1_var if not self.op1_val else self.op1_var + '({})'.format(self.op1_val)
        op2 = self.op2_var if not self.op2_val else self.op2_var + '({})'.format(self.op2_val)
        res = self.res_var if not self.res_val else self.res_var + '({})'.format(self.res_val)
        return "{} = EQ {} {}".format(res, op1,op2)

class TAC_Iszero:
    __internal_name__ = "ISZERO"
    def __init__(self):
        self.op1_var = None
        self.res_var = None
        
        self.op1_val = None
        self.res_val = None

    def parse(self, raw_stmt):
        self.op1_var = raw_stmt.operands[0]
        self.res_var = raw_stmt.defs[0]
        
        self.op1_val = raw_stmt.values.get(self.op1_var, None)
        self.res_val = raw_stmt.values.get(self.res_var, None)

    def handle(self, state):
        pass

    def __str__(self):
        op1 = self.op1_var if not self.op1_val else self.op1_var + '({})'.format(self.op1_val)
        res = self.res_var if not self.res_val else self.res_var + '({})'.format(self.res_val)
        return "{} = ISZERO {}".format(res, op1)

class TAC_And:
    __internal_name__ = "AND"
    def __init__(self):
        self.op1_var = None
        self.op2_var = None
        self.res_var = None
        
        self.op1_val = None
        self.op2_val = None
        self.res_val = None

    def parse(self, raw_stmt):
        self.op1_var = raw_stmt.operands[0]
        self.op2_var = raw_stmt.operands[1]
        self.res_var = raw_stmt.defs[0]
        
        self.op1_val = raw_stmt.values.get(self.op1_var, None)
        self.op2_val = raw_stmt.values.get(self.op2_var, None)
        self.res_val = raw_stmt.values.get(self.res_var, None)

    def handle(self, state):
        pass

    def __str__(self):
        op1 = self.op1_var if not self.op1_val else self.op1_var + '({})'.format(self.op1_val)
        op2 = self.op2_var if not self.op2_val else self.op2_var + '({})'.format(self.op2_val)
        res = self.res_var if not self.res_val else self.res_var + '({})'.format(self.res_val)
        return "{} = AND {} {}".format(res, op1,op2)

class TAC_Or:
    __internal_name__ = "OR"
    def __init__(self):
        self.op1_var = None
        self.op2_var = None
        self.res_var = None
        
        self.op1_val = None
        self.op2_val = None
        self.res_val = None

    def parse(self, raw_stmt):
        self.op1_var = raw_stmt.operands[0]
        self.op2_var = raw_stmt.operands[1]
        self.res_var = raw_stmt.defs[0]
        
        self.op1_val = raw_stmt.values.get(self.op1_var, None)
        self.op2_val = raw_stmt.values.get(self.op2_var, None)
        self.res_val = raw_stmt.values.get(self.res_var, None)

    def handle(self, state):
        pass

    def __str__(self):
        op1 = self.op1_var if not self.op1_val else self.op1_var + '({})'.format(self.op1_val)
        op2 = self.op2_var if not self.op2_val else self.op2_var + '({})'.format(self.op2_val)
        res = self.res_var if not self.res_val else self.res_var + '({})'.format(self.res_val)
        return "{} = OR {} {}".format(res, op1,op2)

class TAC_Xor:
    __internal_name__ = "XOR"
    def __init__(self):
        self.op1_var = None
        self.op2_var = None
        self.res_var = None
        
        self.op1_val = None
        self.op2_val = None
        self.res_val = None

    def parse(self, raw_stmt):
        self.op1_var = raw_stmt.operands[0]
        self.op2_var = raw_stmt.operands[1]
        self.res_var = raw_stmt.defs[0]
        
        self.op1_val = raw_stmt.values.get(self.op1_var, None)
        self.op2_val = raw_stmt.values.get(self.op2_var, None)
        self.res_val = raw_stmt.values.get(self.res_var, None)

    def handle(self, state):
        pass

    def __str__(self):
        op1 = self.op1_var if not self.op1_val else self.op1_var + '({})'.format(self.op1_val)
        op2 = self.op2_var if not self.op2_val else self.op2_var + '({})'.format(self.op2_val)
        res = self.res_var if not self.res_val else self.res_var + '({})'.format(self.res_val)
        return "{} = XOR {} {}".format(res, op1,op2)

class TAC_Not:
    __internal_name__ = "NOT"
    def __init__(self):
        self.op1_var = None
        self.res_var = None
        
        self.op1_val = None
        self.res_val = None

    def parse(self, raw_stmt):
        self.op1_var = raw_stmt.operands[0]
        self.res_var = raw_stmt.defs[0]
        
        self.op1_val = raw_stmt.values.get(self.op1_var, None)
        self.res_val = raw_stmt.values.get(self.res_var, None)

    def handle(self, state):
        pass

    def __str__(self):
        op1 = self.op1_var if not self.op1_val else self.op1_var + '({})'.format(self.op1_val)
        res = self.res_var if not self.res_val else self.res_var + '({})'.format(self.res_val)
        return "{} = NOT {}".format(res, op1)

class TAC_Byte:
    __internal_name__ = "BYTE"
    def __init__(self):
        self.offset_var = None
        self.op2_var = None
        self.res_var = None
        
        self.offset_val = None
        self.op2_val = None
        self.res_val = None

    def parse(self, raw_stmt):
        self.offset_var = raw_stmt.operands[0]
        self.op2_var = raw_stmt.operands[1]
        self.res_var = raw_stmt.defs[0]
        
        self.offset_val = raw_stmt.values.get(self.offset_var, None)
        self.op2_val = raw_stmt.values.get(self.op2_var, None)
        self.res_val = raw_stmt.values.get(self.res_var, None)

    def handle(self, state):
        pass

    def __str__(self):
        offset = self.offset_var if not self.offset_val else self.offset_var + '({})'.format(self.offset_val)
        op2 = self.op2_var if not self.op2_val else self.op2_var + '({})'.format(self.op2_val)
        res = self.res_var if not self.res_val else self.res_var + '({})'.format(self.res_val)
        return "{} = BYTE {} {}".format(res, offset, op2)

class TAC_Shl:
    __internal_name__ = "SHL"
    def __init__(self):
        self.shift_var = None
        self.op2_var = None
        self.res_var = None
        
        self.shift_val = None
        self.op2_val = None
        self.res_val = None

    def parse(self, raw_stmt):
        self.shift_var = raw_stmt.operands[0]
        self.op2_var = raw_stmt.operands[1]
        self.res_var = raw_stmt.defs[0]
        
        self.shift_val = raw_stmt.values.get(self.shift_var, None)
        self.op2_val = raw_stmt.values.get(self.op2_var, None)
        self.res_val = raw_stmt.values.get(self.res_var, None)

    def handle(self, state):
        pass

    def __str__(self):
        shift = self.shift_var if not self.shift_val else self.shift_var + '({})'.format(self.shift_val)
        op2 = self.op2_var if not self.op2_val else self.op2_var + '({})'.format(self.op2_val)
        res = self.res_var if not self.res_val else self.res_var + '({})'.format(self.res_val)
        return "{} = {} << {}".format(res, op2, shift)

class TAC_Shr:
    __internal_name__ = "SHR"
    def __init__(self):
        self.shift_var = None
        self.op2_var = None
        self.res_var = None
        
        self.shift_val = None
        self.op2_val = None
        self.res_val = None

    def parse(self, raw_stmt):
        self.shift_var = raw_stmt.operands[0]
        self.op2_var = raw_stmt.operands[1]
        self.res_var = raw_stmt.defs[0]
        
        self.shift_val = raw_stmt.values.get(self.shift_var, None)
        self.op2_val = raw_stmt.values.get(self.op2_var, None)
        self.res_val = raw_stmt.values.get(self.res_var, None)

    def handle(self, state):
        pass

    def __str__(self):
        shift = self.shift_var if not self.shift_val else self.shift_var + '({})'.format(self.shift_val)
        op2 = self.op2_var if not self.op2_val else self.op2_var + '({})'.format(self.op2_val)
        res = self.res_var if not self.res_val else self.res_var + '({})'.format(self.res_val)
        return "{} = {} >> {}".format(res, op2, shift)

class TAC_Sar:
    __internal_name__ = "SAR"
    def __init__(self):
        self.shift_var = None
        self.op2_var = None
        self.res_var = None
        
        self.shift_val = None
        self.op2_val = None
        self.res_val = None

    def parse(self, raw_stmt):
        self.shift_var = raw_stmt.operands[0]
        self.op2_var = raw_stmt.operands[1]
        self.res_var = raw_stmt.defs[0]
        
        self.shift_val = raw_stmt.values.get(self.shift_var, None)
        self.op2_val = raw_stmt.values.get(self.op2_var, None)
        self.res_val = raw_stmt.values.get(self.res_var, None)

    def handle(self, state):
        pass

    def __str__(self):
        shift = self.shift_var if not self.shift_val else self.shift_var + '({})'.format(self.shift_val)
        op2 = self.op2_var if not self.op2_val else self.op2_var + '({})'.format(self.op2_val)
        res = self.res_var if not self.res_val else self.res_var + '({})'.format(self.res_val)
        return "{} = SAR {} {}".format(res, shift, op2)