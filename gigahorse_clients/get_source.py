#!/usr/bin/env python3
#Copyright (c) 2018, 2019 Neville Grech, Yannis Smaragdakis. All rights reserved.

from collections import defaultdict
from itertools import chain
import argparse
from sympy import sympify
import json
import pdb, traceback, sys, os

sys.setrecursionlimit(3000)

parser = argparse.ArgumentParser(description =
    'A source decompiler from functional 3-address IR to Solidity-like code.'
)

parser.add_argument("-d",
                    "--development",
                    action="store_true",
                    default=False,
                    help="Development Mode.")

parser.add_argument("-v",
                    "--verbose",
                    action="store_true",
                    default=False,
                    help="Verbose Warnings Mode.")


def render_set(a):
    if len(a) == 1:
        return list(a)[0]
    return '{'+', '.join(a) + '}'

def sort_addresses_key(x):
    try:
        return int(x.split('0x')[1], 16)
    except:
        return -1


EXPRESSION_COMPLEXITY_CUTOFF = 60
def minimize_expression_complexity(stmts):
    ''' Greedy algorithm for minimizing expression complexity through inlining '''
    done = set()
    for s in sorted(stmts, key = lambda a : sort_addresses_key(a.stmt)):
        if s.too_complex:
            continue
        if s in done:
            continue
        done.add(s)
        complexity = s.num_operators + sum(
            op.complexity for op in s.operand_exprs
        )
        if (complexity * len(s.used_by)) < EXPRESSION_COMPLEXITY_CUTOFF:
            s.inlineable = True
            s.complexity = complexity
            for op in s.operand_exprs:
                done.add(op)

def guess_private_function_names():
    names = defaultdict(list)
    taken = set()
    def function_size(f):
        return sum(len(tac_blocks[k]) for k, v in in_function.items() if f in v)
    for k, to in function_calls.items():
        to = list(to)[0]
        if to in public_functions:
            continue
        fro = list(in_function[k])[0]
        if high_level_function_name[fro].startswith('0x'):
            # not really a "high level" name
            continue
        if fro in taken:
            continue
        taken.add(fro)
        fro_size = function_size(fro)
        to_size = max(function_size(to), 1)
        generated_name = high_level_function_name[fro].split('(')[0]+'_impl'
        names[to].append((generated_name, fro_size / to_size))
    for k, v in names.items():
        high_level_function_name[k] = sorted(v, key = lambda a : a[1])[0][0]

def guess_storage_names():
    high_level_storage_name = {}
    def from_function_name(f):
        name = f.split('(')[0]
        for r in ['get', 'set']:
            name = name.replace(r, '')
        name = name[0].lower() + name[1:]
        return name

    def function_stmts(f):
        return list(chain(*(tac_blocks[k] for k, v in in_function.items() if f in v)))
    names = defaultdict(list)
    for f in functions:
        if high_level_function_name[f].startswith('0x'):
            # not really a "high level" name
            continue
        stmts = function_stmts(f)
        for stmt, g in known_storage:
            if stmt in stmts:
                names[g].append((
                    from_function_name(high_level_function_name[f]),
                    len(stmts)
                ))
                break
    for k, v in names.items():
        high_level_storage_name[k] = sorted(v, key = lambda a : a[1])[0][0]
    for stmt, g in known_storage:
        if g in high_level_storage_name:
            continue
        if g in owner_store:
            if len(owner_store) == 1:
                high_level_storage_name[g] = 'owner'
            else:
                high_level_storage_name[g] = 'owner_'+g[2:]
        else:
            if g in map_id_to_storage_index:
                high_level_storage_name[g] = 'map_'+g[2:]
            elif g in array_id_to_storage_index:
                high_level_storage_name[g] = 'array_'+g[2:]
            else:
                high_level_storage_name[g] = 'storage_'+g[2:]
                
                
            
    return high_level_storage_name

args = parser.parse_args()

class SourceStatementList:
    def __init__(self, inner = None):
        if inner:
            self.inner = inner
        else:
            self.inner = []
    def append(self, stmt):
        if stmt:
            assert isinstance(stmt, str)
            self.inner.append(stmt)

    def prepend_comment(self, comment):
        if self.inner:
            self.inner[0] = self.inner[0] + ' // '+comment
        else:
            self.inner.append('// ' + comment)

    def __add__(self, other):
        return SourceStatementList(self.inner + other.inner)
    
    def append_empty_line(self):
        self.inner.append('')

    def append_indent(self, stmts, braces = False):
        if stmts:
            self.append('\n'.join('  '+s for s in stmts.split('\n')))

    def __len__(self):
        return len(self.inner)
    
    def __str__(self):
        return '\n'.join(self.inner)
        

def warning(*args):
    print(*args, file = sys.stderr)

def get_const(a, default = None):
    try:
        return int(a, 16)
    except:
        return default

def parseCsv(name):
    try:
        f = open(name+'.csv')
        return [line.strip('\n \t\r').split('\t') for line in f]
    except Exception:
        warning('WARNING: %s not found'%name)
        return []

def parseCsvDict(name):
    as_tuples = parseCsv(name)
    res = dict(as_tuples)
    if args.verbose:
        for k, v in as_tuples:
            v2 = res[k]
            if v2 != v:
                warning('WARNING: %(v)s and %(v2)s map to same key %(k)s in %(name)s'%locals())
    return res

def parseCsvDict(name):
    ''' With bias '''
    as_tuples = parseCsv(name)
    card = defaultdict(int)
    for k, v in as_tuples:
        card[v] += 1
    res = {}
    for k, v in as_tuples:
#        if k in res and card[res[k]] < card[v]:
#            continue
        if k in res and res[k] < v:
            continue
        res[k] = v
    if args.verbose:
        for k, v in as_tuples:
            v2 = res[k]
            if v2 != v:
                warning('WARNING: %(v)s and %(v2)s map to same key %(k)s in %(name)s'%locals())
    return res


def parseCsvMultiDict(name):
    res = defaultdict(set)
    for k, v in parseCsv(name):
        res[k].add(v)
    return dict(res)

def load_tac_blocks():
    out = defaultdict(list)
    for s, b in parseCsv('TAC_Block'):
        out[b].append(s)
    return {k:sorted(ss, key = lambda x: get_const(x, 0)) for k, ss in out.items()}

def load_tac_sorted(prop):
    out = defaultdict(list)
    for s, v, n in parseCsv(prop):
        n = int(n)
        while n > len(out[s]) - 1:
            out[s].append('')
        if n<0:
            out[s].append(v)
        else:
            out[s][n] = v
    return out
def untuple(tuples):
    return [t[0] for t in tuples]

class DefensiveStringList(list):
    def __getitem__(self, n):
        if isinstance(n, int):
            if n >= len(self):
                return ''
            if -1-n >= len(self):
                return ''
        return super().__getitem__(n)

tac_blocks = defaultdict(list,load_tac_blocks())

tac_use = load_tac_sorted('TAC_Use')
tac_def = load_tac_sorted('TAC_Def')
tac_op = parseCsvDict('TAC_Op')

highlevel_op = parseCsvDict('HighLevel_Op')
highlevel_use = load_tac_sorted('HighLevel_Use')
highlevel_structure = parseCsvDict('HighLevel_Structure')

function_arguments = load_tac_sorted('FormalArgs')
high_level_function_name = parseCsvDict('HighLevelFunctionName')
functions = untuple(parseCsv('Function'))
public_functions = set(untuple(parseCsv('PublicFunction')))
public_functions.add('0x0')

temp_stmt = untuple(parseCsv('TempStmt'))

function_entries = untuple(parseCsv('IRFunctionEntry'))
in_function = parseCsvMultiDict('InFunction')
in_loop = parseCsvMultiDict('BlockInStructuredLoop')
loop_exit_condition = parseCsvMultiDict('LoopExitCond')
if_then_else_head = untuple(parseCsv('IfThenElseHead'))
in_if_then_else_consequent = parseCsvMultiDict('IfThenElseConsequent')
in_if_then_else_alternative = parseCsvMultiDict('IfThenElseAlternative')
scope_scope = parseCsvMultiDict('Scope_Scope')
statement_scope = parseCsvMultiDict('Statement_Scope')

# data structures
map_id_to_storage_index = parseCsvDict('MapIdToStorageIndex')
array_id_to_storage_index = parseCsvDict('ArrayIdToStorageIndex')

owner_store = set(untuple(parseCsv('SenderGuard')))

known_storage = parseCsv('KnownStorage')

high_level_storage_name = guess_storage_names()

variable_phimap = defaultdict(lambda a : a)
def build_phi_map():
    for stmt, phi in tac_op.items():
        if phi != 'PHI':
            continue
        for v in tac_use[stmt]:
            variable_phimap[v] = tac_def[stmt][0]
    # poor man's fixpoint
    for i in range(10):
        for v_old, v_new in variable_phimap.items():
            if v_new in variable_phimap:
                variable_phimap[v_old] = variable_phimap[v_new]

build_phi_map()

def format_var(v):
    if v in variable_phimap:
        v = variable_phimap[v]
    return 'v' + v.replace('0x', '')

variable_value = parseCsvDict('TAC_Variable_Value') # or multidict ?
if_then_else_predicate = parseCsvMultiDict('IfThenElsePredicate')
if_then_else_predicate_stmt = parseCsvDict('IfThenElsePredicateStmt')



function_calls = parseCsvMultiDict('IRFunctionCall')

function_call_return = {a[0] : (a[1], a[2]) for a in parseCsv('IRFunctionCallReturn')}


edges = parseCsv('LocalBlockEdge')

reachable = list(chain(function_entries, *edges))

guess_private_function_names()

def expand_stringlist(lst, n):
    for s in lst:
        n-=1
        yield s
    yield from ['']*n

def expand_formatstring(lst, n):
    return tuple(expand_stringlist(lst, n))

class Renderable:
    def __lt__(self, other):
        if self.block == other.block:
            return sort_addresses_key(self.stmt) < sort_addresses_key(other.stmt)
        return self.block < other.block

    def render_all_statements(self):
        raise NotImplementedError("Not impl.")

class Stmt(Renderable):
    opcodes = []
    num_operators = 1
    side_effect = True
    too_complex = False
    
    def __init__(self, scope, stmt, variable, opcode, *operands):
        self.inlineable = False
        self.complexity = 1
        self.stmt = stmt
        self.used_by = set()
        assert isinstance(variable, list)
        self.variable = variable
        self.formatted_variable = list(map(format_var, variable))
        self.opcode = opcode
        self.operands = operands
        self.my_scope = scope
        scope.append_children(self)
        self.block = cfg.statement_block(stmt)
        self.init()

    def init(self):
        ''' initializer that can be utilized by subclasses '''
        pass

    def is_const(self, ttl = 10):
        return False

    def is_cast(self):
        return False

    def is_needed(self, ttl = 10):
        if ttl < 1:
            return True
        return self.side_effect or any(a.is_needed(ttl-1) for a in self.used_by)
    
    def get_variable_type(self, i):
        return 'uint256'
    
    def resolve_usages(self, exprs):
        # exprs indexed by variable
        self.operand_exprs = []
        for operand in self.operands:
            if operand in exprs:
                operand_expr = exprs[operand]
            else:
                operand_expr = UnknownStmt(operand)
            self.operand_exprs.append(operand_expr)
        for v in self.operands:
            if v in exprs:
                exprs[v].used_by.add(self)

    def render(self, v):
        return self.my_scope.render_stmt(self, v)

    def preamble(self):
        if self.stmt in temp_stmt:
            return ''
        return self.my_scope.preamble_stmt(self)

    def render_all_statements(self):
        preamble = self.preamble()
        if len(preamble):
            return preamble+';'
        return ''
    
    @classmethod
    def from_opcode(cls, scope, stmt, variable, opcode, *operands):
        for new_cls in cls.__subclasses__():
            if opcode in new_cls.opcodes:
                return new_cls(scope, stmt, variable, opcode, *operands)
        return DefaultStmt(scope, stmt, variable, opcode, *operands)


    @property
    def rendered_operands(self):
        return DefensiveStringList(op.render(var) for var, op in zip(self.operands, self.operand_exprs))

    def __eq__(self, other):
        return isinstance(other, Stmt) and self.stmt == other.stmt

    def __hash__(self):
        return hash(self.stmt) + 33

class SimpleRValue:
    num_operators = 0
    
    def preamble_impl(self):
        if not self.inlineable:
            variable = self.formatted_variable[0]
            expr = self._render()
            return '%(variable)s = %(expr)s'%locals()
        else:
            return ''

    def render_impl(self, v):
        assert v in self.variable, v
        if not self.inlineable:
            return format_var(v)
        else:
            return self._render()
        
class BinOpStmt(Stmt, SimpleRValue):
    side_effect = False
    num_operators = 1
    opcodes = {
        'ADD' : '+',
        'SUB' : '-',
        'MUL' : '*',
        'DIV' : '/',
        'AND' : '&',
        'OR'  : '|',
        'XOR' : '^',
        'SGT' : '>=',
        'GT'  : '>',
        'SAR' : '>>',
        'EXP' : '**',
        'EQ'  : '==',
        'SDIV': '/',
        'SHR' : '>>',
        'SLT' : '<=',
        'SMOD': '%',
        'SHL' : '<<',
        'LT'  : '<',
        'MOD' : '%',
    }

    simplifyable = ['ADD', 'SUB', 'MUL', 'DIV', 'AND', 'OR',
                    'XOR', 'EXP', 'SDIV', 'SMOD', 'MOD']

    def init(self):
        self.give_up_simplification = False

    def is_const(self, ttl = 10):
        if ttl < 1:
            return False
        return all(o.is_const(ttl-1) for o in self.operand_exprs)

    def _render(self):
        if self.variable[0] in variable_value:
            value = variable_value[self.variable[0]]
            if value.startswith('0x'):
                return value
        res = '(' + (' %s '%self.opcodes[self.opcode]).join(self.rendered_operands) + ')'
        if self.opcode in self.simplifyable and not self.give_up_simplification:
            # constant folding
            try:
                res = eval('hex'+res)
            except Exception:
                try:
                    res = str(sympify(res))
                except Exception:
                    # memoization, avoid re-computing only on failure
                    self.give_up_simplification = True
        if self.opcode != 'AND':
            return res
        else:
            return self.cast_optimize(res)


    cast_masks = {
        0xffffffffffffffffffffffffffffffffffffffff: 'address',
        0xff: 'uint8',
        0xffff: 'uint16',
        0xffffffff: 'uint32',
        0xffffffffffffffff: 'uint64',
        0xffffffffffffffffffffffffffffffff: 'uint128',
        0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff: 'uint256',
    }

    def is_cast(self):
        self.constoperand = None
        self.castoperand = None
        for operand, operand_expr in zip(self.rendered_operands, self.operand_exprs):
            try:
                self.constoperand = int(operand, 16)
            except:
                self.castoperand = operand_expr
        if self.constoperand and self.castoperand and (self.constoperand in self.cast_masks):
            return True
        return False

    def get_variable_type(self, i):
        if i == 0 and self.is_cast():
            return self.cast_masks[self.constoperand]
    
    def cast_optimize(self, res):
        if not self.is_cast():
            return res
        return (
            self.cast_masks[self.constoperand] +
            '(' + self.castoperand.render(self.castoperand.variable[0]) + ')'
        )
            
            
    
class UnOpStmt(Stmt, SimpleRValue):
    side_effect = False
    num_operators = 1
    opcodes = {
        'BYTE' : '(byte) %s',
        'SIGNEXTEND' : 'dunno %s',
        'ISZERO' : '!%s',
        'NOT'    : '~%s',
    }

    def _render(self):
        res = self.opcodes[self.opcode]%self.rendered_operands[0]
        if res.startswith('!!'):
            return res[2:]
        else:
            return res
    

class TernOpStmt(Stmt, SimpleRValue):
    side_effect = False
    num_operators = 2
    opcodes = {'ADDMOD' : '(%s + %s) %% %s',
               'MULMOD' : '(%s * %s) %% %s'}

    def _render(self):
        return self.opcodes[self.opcode]%expand_formatstring(self.rendered_operands, 3)

class ConstStmt(Stmt, SimpleRValue):
    side_effect = False
    num_operators = 0
    opcodes = ['CONST']
    operand_exprs = []

    def is_const(self, ttl = 10):
        return True
    
    def init(self):
        self.variable_value = variable_value[self.variable[0]]
        
    def _render(self):
        return self.variable_value


class ADDRESSStmt(Stmt, SimpleRValue):
    side_effect = False
    num_operators = 0
    opcodes = ['ADDRESS']

    def _render(self):
        return 'this'


class SHA3Stmt(Stmt, SimpleRValue):
    side_effect = False
    num_operators = 1
    opcodes = ['SHA3']

    def _render(self):
        return 'keccak256(%s, %s)'%expand_formatstring(self.rendered_operands, 2)

class NoLValue:
    too_complex = True

    def preamble_impl(self):
        return self._render()

    def render_impl(self, v):
        warning('Not suitable as expression: ', v, self.stmt)
        return v
    
class JUMPIStmt(Stmt, NoLValue):
    opcodes = ['JUMPI']
    def _render(self):
        res = 'if (%s) GOTO %s'%expand_formatstring(self.rendered_operands, 2)[::-1]
        return res

class THROWIStmt(Stmt, NoLValue):
    opcodes = ['THROWI']
    def _render(self):
        return 'require(%s == 0)'%self.rendered_operands[0]

class CALLPrivate:
    def get_target(self):
        block = cfg.statement_block(self.stmt)
        #TODO: virtual calls
        target = list(function_calls[block.b])[0]
        fn = high_level_function_name[target]
        return fn
        
class CALLPRIVATEIStmt(Stmt, CALLPrivate):
    opcodes = ['CALLPRIVATEI']
    too_complex = True

    def preamble_impl(self):
        fn = self.get_target()
        cond = self.rendered_operands[1]
        operands = ', '.join(self.rendered_operands[2:])
        ret = ', '.join(self.formatted_variable)
        if ret: ret += ' = '
        return 'if (%s) %s%s(%s)'%(cond, ret, fn, operands)

    def render_impl(self, var):
        return format_var(var)

    
class CALLPRIVATEStmt(Stmt, CALLPrivate):
    opcodes = ['CALLPRIVATE']
    too_complex = True

    def preamble_impl(self):
        # first get block
        fn = self.get_target()
        operands = ', '.join(self.rendered_operands[1:])
        ret = ', '.join(self.formatted_variable)
        if ret: ret += ' = '
        return '%s%s(%s)'%(ret, fn, operands)

    def render_impl(self, var):
        return format_var(var)

class RETURNPRIVATEStmt(Stmt):
    opcodes = ['RETURNPRIVATE']
    too_complex = True

    def preamble_impl(self):
        # first get block
        target = self.rendered_operands[0]
        operands = ', '.join(self.rendered_operands[1:])
        return 'return(%s) // to %s'%(operands, target)

    def render_impl(self, var):
        return format_var(var)

class RETURNStmt(Stmt):
    opcodes = ['RETURN']
    too_complex = True

    def preamble_impl(self):
        # first get block
        start = self.rendered_operands[0]
        length = self.rendered_operands[1]
        return 'return(MEM[%(start)s:%(start)s + %(length)s])'%locals()

    def render_impl(self, var):
        return format_var(var)


    
class JUMPStmt(Stmt, NoLValue):
    opcodes = ['JUMP']
    def _render(self):
        return 'GOTO %s'%expand_formatstring(self.rendered_operands, 1)

class MemoryFormat:
    def get_memexpr(self):
        rendered_operand = expand_formatstring(self.rendered_operands, 1)[0]
        const_address = get_const(rendered_operand)
        if const_address is None or const_address > 0xFFFFFFFF:
            return self.longname+'[%s]'%rendered_operand
        return self.shortname+str(const_address)
        
class MSTOREStmt(Stmt, NoLValue, MemoryFormat):
    opcodes = ['MSTORE']
    longname = "MEM"
    shortname = "M"
    side_effect = True
    
    def _render(self):
        if len(self.rendered_operands) < 2:
            return ''
        return '%s = %s'%(self.get_memexpr(), self.rendered_operands[1])
        
class MLoadStmt(Stmt, SimpleRValue, MemoryFormat):
    side_effect = False
    num_operators = 2
    opcodes = ['MLOAD']
    longname = "MEM"
    shortname = "M"

    def _render(self):
        return self.get_memexpr()
        
class StoreFormat(MemoryFormat):
    longname = "STORAGE"
    shortname = "S"
    def get_memexpr(self):
        high_level_name = high_level_storage_name.get(self.rendered_operands[0], None)
        if high_level_name:
            return high_level_name
        rendered = super().get_memexpr()
        return rendered
    
class SSTOREStmt(Stmt, NoLValue, StoreFormat):
    opcodes = ['SSTORE']
    def _render(self):
        if len(self.rendered_operands) < 2:
            return ''
        return '%s = %s'%(self.get_memexpr(), self.rendered_operands[1])

class SLoadStmt(Stmt, SimpleRValue, StoreFormat):
    num_operators = 2
    opcodes = ['SLOAD']

    def _render(self):
        return self.get_memexpr()
    
class PHIStmt(Stmt):
    side_effect = False
    opcodes = ['PHI']

    def preamble_impl(self):
        return ''
        '%s = PHI(...)'%self.formatted_variable[0]

    def render_impl(self, v):
        return format_var(v)
    
class DefaultStmt(Stmt):

    opcodes = []

    translations = {
        'CALLER': 'msg.sender',
        'CALLVALUE': 'msg.value',
        'BLOCKHASH': 'block.blockhash',
        'COINBASE': 'block.coinbase',
        'DIFFICULTY': 'block.difficulty',
        'GASLIMIT': 'block.gaslimit',
        'NUMBER': 'block.number',
        'GAS': 'msg.gas',
        'TIMESTAMP': 'now',
        'GASPRICE': 'tx.gasprice',
        'ORIGIN': 'tx.origin',
        'SELFDESTRUCT': 'selfdestruct',
    }
 
    def init(self):
        self.opcode_function = self.translations.get(self.opcode, self.opcode)
        self.too_complex = not bool(self.formatted_variable)

    def preamble_impl(self):
        if self.inlineable:
            return ''
        if self.formatted_variable:
            prepend = self.formatted_variable[0] + ' = '
        else:
            prepend = ''
        return prepend + self.render_rhs()

    def render_rhs(self):
        if self.rendered_operands:
            operands = '(%s)'%(', '.join(self.rendered_operands))
        else:
            operands = ''
        return self.opcode_function + operands
        
    def render_impl(self, v):
        if not self.inlineable:
            return format_var(v)
        return self.render_rhs()
    
class CallDataLoadStmt(Stmt, SimpleRValue):
    opcodes = ['CALLDATALOAD']
    def _render(self):
        operand = self.rendered_operands[0]
        if operand == '0x0':
            return 'msg.sig'
        return 'msg.data[%s]'%operand

class ExtCodeSizeStmt(Stmt, SimpleRValue):
    opcodes = ['EXTCODESIZE']
    def _render(self):
        return 'isContract(%s)'%self.rendered_operands[0]

class CallDataSizeStmt(Stmt, SimpleRValue):
    opcodes = ['CALLDATASIZE']
    def _render(self):
        return 'msg.data.length()'
    
class CallStmt(Stmt, SimpleRValue):
    opcodes = ['CALL', 'DELEGATECALL']

    def _render(self):
        # call(g, a, v, in, insize, out, outsize)
        # call contract at address a with input mem[in..(in+insize))
        # providing g gas and v wei and
        # output area mem[out..(out+outsize))
        # returning 0 on error (eg. out of gas) and 1 on success
        #TODO render precompiled functions 0x1 to 0x4
        g, a, v, inp, insize, out, outsize = expand_formatstring(
            self.rendered_operands, 7
        )
        op = self.opcode.lower()
        if v == '0x0':
            value = ''
        else:
            value = '.value(%s)'%v
        # , MEM[%(out)s : %(out)s + %(outsize)s]
        return '%(a)s.%(op)s(MEM[%(inp)s : %(inp)s + %(insize)s])%(value)s.gas(%(g)s)'%locals()
    

class StopStmt(Stmt, NoLValue):
    opcodes = ['STOP','MISSING']
    def _render(self):
        return 'exit()'

class ThrowStmt(Stmt, NoLValue):
    opcodes = ['THROW', 'REVERT']
    def _render(self):
        return 'throw()'

class LogStmt(Stmt, NoLValue):
    opcodes = ['LOG%d'%i for i in range(10)]

    def _render(self):
        return 'log(%s)'%(', '.join(self.rendered_operands))

class UnknownStmt(Stmt):

    def __init__(self, var):
        self.complexity = 100
        self.variable = [var]
        self.formatted_variable = [format_var(var)]
        self.operands = []
        self.stmt = 'unknown ' + var
        self.opcode = ''
        self.operand_exprs = []
        self.used_by = []
        self.my_scope = contract_scope
        contract_scope.append_children(self)

    def preamble_impl(self):
        return ''

    def render_impl(self, v):
        return format_var(v)

# Higher level statements for data structures
class DataStructureRelated(Stmt):
    def init(self):
        self.data_structure = highlevel_structure[self.stmt]

        self.data_structure_formatted = high_level_storage_name.get(
            self.data_structure, None
        )

        if not self.data_structure_formatted:
            data_id = self.data_structure[2:]
            self.data_structure_formatted = 'data_'+data_id

    

class SETSize(DataStructureRelated,Stmt,NoLValue):
    opcodes = ['SETSIZE']

    def _render(self):
        return '%s.length = %s'%(
            self.data_structure_formatted,
            self.rendered_operands[0]
        )

class GETSize(DataStructureRelated,Stmt,SimpleRValue):
    opcodes = ['GETSIZE']

    def _render(self):
        return '%s.length'%self.data_structure_formatted
        
class SETElementStmt(DataStructureRelated,Stmt,NoLValue):
    opcodes = ['SETELEMENT']
    
    def _render(self):
        data_structure = self.data_structure_formatted
        index = self.rendered_operands[0]
        if len(self.rendered_operands) > 2:
            element = self.rendered_operands[1]
            element_lvalue = '['+element+']'
        else:
            element_lvalue = ''
        var = self.rendered_operands[-1]
        var_rvalue = ' = '+var if var else ''
        return '%(data_structure)s[%(index)s]%(element_lvalue)s%(var_rvalue)s'%locals()

class GETElementStmt(DataStructureRelated,Stmt,SimpleRValue):
    
    opcodes = ['GETELEMENT']

    def _render(self):
        data_structure = self.data_structure_formatted
        index = self.rendered_operands[0]
        element = self.rendered_operands[1]
        element_lvalue = '['+element+']' if element else ''
        return '%(data_structure)s[%(index)s]%(element_lvalue)s'%locals()      

    
class Scope(Renderable):

    @classmethod
    def from_ids(cls, ids):
        if len(ids) > 2:
            # sanity checking: multiple function scopes only
            ids_sanitized = [id for id in ids if id.startswith('f') and id in scopes]
            if len(ids_sanitized) < len(ids):
                warning('Invalid scope combination: %s'%str(ids))
            ids = ids_sanitized
        if len(ids) == 0:
            return contract_scope
        if len(ids) == 1:
            return scopes.get(list(ids)[0], contract_scope)
        else:
            return MultiFunctionScopeAdapter(scopes[s] for s in ids)

    def __init__(self):
        self.children = []

    def append_children(self, child):
        self.children.append(child)

    def resolve_scope(self, exprs):
        pass

    def assert_acyclical(self):
        # check that scoping is acyclical
        curr_scope = self
        for i in range(20):
            if curr_scope == contract_scope:
                return
            curr_scope = curr_scope.my_scope
        assert False, "Probable Cycle detected in scoping"
    
    def preamble_stmt(self, stmt):
        return self.my_scope.preamble_stmt(stmt)

    def render_stmt(self, stmt, variable):
        return self.my_scope.render_stmt(stmt, variable)

    def __eq__(self, other):
        return type(self) == type(other) and self.scope_id == other.scope_id

    def __hash__(self):
        return hash(self.scope_id) + 32

    def log_lines(self, lines):
        return lines
        return '\n'.join(str(self) + ": " + l for l in lines.split('\n'))

    def __repr__(self):
        return '<%s with id %s>'%(str(type(self)), self.scope_id)

    __str__ = __repr__

class ContractScope(Scope):

    def __init__(self, function_scopes):
        self.scope_id = 'contract_scope'
        self.function_scopes = function_scopes
        self.my_scope = None
        super().__init__()


    def get_abi(self):
        function_scopes_items = sorted(
            list(self.function_scopes.items()),
            key = lambda a: a[0]
        )
        output = []
        for _, f in function_scopes_items:
            if not f.is_public:
                continue
            name = f.name
            output.append(dict(
                name = name,
                type = "function",
                inputs = [
                    dict(name = n, type = t) for t,n in f.get_arg_types_and_names()
                ]
            ))
        return output

    def render_all_statements(self):
        lines = SourceStatementList()
        # don't forget the public variables
        lines.append('contract Contract {')
        lines.append_empty_line()
        lines.append_indent(self.render_all_datastructures())
        lines.append_empty_line()
        function_scopes_items = sorted(
            list(self.function_scopes.items()),
            key = lambda a: a[0]
        )
        for _, f in function_scopes_items:
            lines.append_indent(f.render_all_statements())
            lines.append_empty_line()
        lines.append('}')
        return self.log_lines(str(lines))

    def render_all_datastructures(self):
        data = {}
        for id in map_id_to_storage_index:
            data[id] = 'mapping (uint256 => ?) %s;'%high_level_storage_name[id]
        for id in array_id_to_storage_index:
            data[id] = 'array[] %s;'%high_level_storage_name[id]
            
        for k, v in high_level_storage_name.items():
            if k not in data:
                data[k] = 'uint256 %s; // %s'%(v, k)

        lines = SourceStatementList()
        data = sorted(list(data.items()), key = lambda a: a[0])
        for k, v in data:
            lines.append(v)
        return str(lines)


    def preamble_stmt(self, stmt):
        if not stmt.is_needed():
            return ''
        block = cfg.statement_block(stmt.stmt)
        if stmt.opcode == 'JUMP':
            if all(block.is_next_linear(cfg.get_block(b))
                   for b in block.next_block()):
                return ''
        # jumpi that can be eliminated
        if stmt.opcode == 'JUMPI' and len(block.next_concrete_block()) < 2:
            return ''
        return stmt.preamble_impl()

    def render_stmt(self, stmt, variable):
        return stmt.render_impl(variable)

class LoopScope(Scope):
    def __init__(self, loop):
        self.scope_id = 'l'+loop
        self.loop = loop
        self.block = cfg.get_block(loop)
        self.stmt = 'loop'
        super().__init__()

    def render_all_statements(self):
        stmts = SourceStatementList()
        stmts.append('while (true) {')
        rendered_statements = {}
        for child in sorted(self.children):
            stmts.append_indent(child.render_all_statements())
        stmts.append('}')
        return self.log_lines(str(stmts))

    def preamble_stmt(self, stmt):
        if stmt.opcode == 'JUMP' and stmt.rendered_operands[-1] == self.loop:
            return 'continue'
        if stmt.opcode == 'JUMPI':
            predicate = stmt.operand_exprs[1]
            variable = predicate.variable[0]
            if self.loop in loop_exit_condition.get(variable, []):
                res = 'if (%s) break'%predicate.render(variable)
                return res
        return super().preamble_stmt(stmt)

    
class IfThenElseScope(Scope):
    def __init__(self, structure):
        self.structure = structure
        self.scope_id = 'i'+structure
        self.block = cfg.get_block(structure)
        self.stmt = if_then_else_predicate_stmt[structure]
        super().__init__()

    def resolve_scope(self, vars):
        for v, expr in vars.items():
            if self.structure in if_then_else_predicate.get(v, []):
                self.predicate = expr
                return
        self.predicate = UnknownStmt('UNKNOWN_PREDICATE')
        
    def preamble_stmt(self, stmt):
        if stmt.opcode == 'JUMPI' and stmt.operand_exprs[1] == self.predicate:
            return '' # we'll render it elsewhere
        return super().preamble_stmt(stmt)

    def render_predicate(self, invert = False):
        predicate = self.predicate
        prepend = ''
        if invert:
            if predicate.opcode == 'ISZERO':
                if not predicate.operand_exprs:
                    return '?'
                predicate = predicate.operand_exprs[0]
            else:
                prepend = '!'
        return prepend + predicate.render(predicate.variable[0])


    def is_consequent_inlinable(self):
        # my consequent is an if-then-else
        inner_scope = set()
        if len(self.children) != 1:
            return False
        child = self.children[0]
        if child.preamble():
            return False
        if not isinstance(child, IfThenElseScope):
            return False
        return str(self.render_alternative()).strip().startswith('throw()')

    def render_branch(self, branch):
        stmts = SourceStatementList()
        for child in sorted(self.children):
            if self.structure in branch.get(child.block.b, []):
                stmts.append(child.render_all_statements())
        return stmts

    def render_consequent(self):
        return self.render_branch(in_if_then_else_consequent)

    def render_alternative(self):
        return self.render_branch(in_if_then_else_alternative)
    
    def render_inline_predicate(self):
        predicate = self.render_predicate()
        if self.is_consequent_inlinable():
            predicate += ' && ' + self.inner_scope.render_inline_predicate()
        return predicate

    def render_inline_consequent(self):
        if self.is_consequent_inlinable():
            return self.inner_scope.render_inline_consequent()
        else:
            return self.render_consequent()
        
    def render_all_statements(self):
        stmts = SourceStatementList()

        if self.is_consequent_inlinable():
            stmts.append('require(%s);'%self.render_inline_predicate())
            stmts.append(str(self.render_inline_consequent()))
            return str(stmts)
        preamble = self.predicate.preamble()
        stmts.append(preamble)
        consequent_rendered = self.render_branch(in_if_then_else_consequent)
        alternative_rendered = self.render_branch(in_if_then_else_alternative)
        if str(alternative_rendered).strip().startswith('throw'):
            stmts.append('require(%s == 0)'%self.render_predicate())
            stmts += consequent_rendered
            return str(stmts)

        # a normal if then else
        if not consequent_rendered:
            consequent_rendered = alternative_rendered
            alternative_rendered = SourceStatementList()
            head = 'if (%s) {'%self.render_predicate(invert = True)
        else:
            head = 'if (%s) {'%self.render_predicate()
            
        stmts.append(head)
        stmts.append_indent(str(consequent_rendered))
        if alternative_rendered:
            stmts.append('} else {')
            stmts.append_indent(str(alternative_rendered))
        stmts.append('}')
        return self.log_lines(str(stmts))

class MultiFunctionScopeAdapter(Scope):
    def __init__(self, scopes):
        self.scopes = list(scopes)

    def append_children(self, child):
        for scope in self.scopes:
            scope.append_children(child)
    
    def resolve_scope(self, exprs):
        for scope in self.scopes:
            scope.resolve_scope(exprs)

    def render_stmt(self, expr, v):
        return self.scopes[0].render_stmt(expr, v)

    def preamble_stmt(self, stmt):
        return self.scopes[0].preamble_stmt(stmt)

    def __str__(self):
        return 'MultiFunctionScopeAdapter([%s])'%(', '.join(str(s) for s in self.scopes))

class FunctionScope(Scope):
    is_public = False

    def render_all_statements(self):
        stmts = SourceStatementList()
        stmts.append(self.get_function_signature() + ' {')
        for child in sorted(self.children):
            stmts.append_indent(child.render_all_statements())
        stmts.append('}')
        return self.log_lines(str(stmts))
  

class PrivateFunctionScope(FunctionScope):

    def __init__(self, function):
        self.scope_id = 'f'+function
        self.function = function
        self.stmt = self.scope_id
        FunctionScope.__init__(self)

    def get_function_signature(self):
        return ("function %s(%s) private"%(
                high_level_function_name[self.function],
                ', '.join('uint256 '+format_var(v) for v in function_arguments[self.function]))
            )
    

class PublicFunctionScope(FunctionScope):
    is_public = True
    
    def __init__(self, function):
        self.scope_id = 'f'+function
        self.const_to_name = {}
        self.function = function
        fnName = high_level_function_name[self.function]
        self.operand_types = []
        self.exprs = set()
        if '(' in fnName:
            self.name, self.operand_types = self.parse(fnName)
            n_args = len(self.operand_types)
        else:
            self.name = fnName
        super().__init__()
        
    def parse(self, highlevelFnName):
        name, rest = highlevelFnName.split('(')
        rest = rest[:-1]
        return name, rest.split(',')

    def get_child_calldataloads(self, child):
        if isinstance(child, Stmt):
            if child.opcode == 'CALLDATALOAD':
                return [child]
            else:
                return []
        return chain(*(self.get_child_calldataloads(c) for c in child.children))
    
    def resolve_scope(self, exprs):
        self.calldataloads = set(self.get_child_calldataloads(self))

        # is a cast statement that contains a constant calldataload
        calldataloadconsts = set()
        for expr in self.calldataloads:
            if not(expr.operand_exprs):
                continue
            operand = expr.operand_exprs[0]
            const = get_const(operand.render_impl(operand.variable[0]))
            if const is not None:
                calldataloadconsts.add(const)
        sorted_consts = sorted(list(calldataloadconsts))

        self.inferred_types = ['uint%d'%((end-start)*8) for start, end in zip(sorted_consts, sorted_consts[1:])]
        if calldataloadconsts:
            self.inferred_types.append('uint256')
        self.inferred_const_to_type = dict(zip(sorted_consts, self.inferred_types))
        self.const_to_name = {v: ('varg%d'%i) for i,v in enumerate(sorted_consts)}
        self.const_to_name[0] = 'function_selector'
        self.sorted_consts = sorted_consts
        

    def get_calldataloadconst(self, expr):
        inferred_type = None
        cast_expr = expr
        if expr.is_cast():
            inferred_type = expr.get_variable_type(0)
            expr = expr.castoperand
        div_expr = expr
        if expr.opcode in ['DIV', 'SHR']:
            expr = expr.operand_exprs[0]
        if expr.opcode == 'CALLDATALOAD':
            const = get_const(expr.rendered_operands[0])
            if const in self.const_to_name:
                if inferred_type:
                    self.inferred_const_to_type[const] = inferred_type
                return const

    def render_stmt(self, expr, v):
        const = self.get_calldataloadconst(expr)
        if const is not None:
            return self.const_to_name[const]
        return expr.render_impl(v)

    def preamble_stmt(self, stmt):
        const = self.get_calldataloadconst(stmt)
        if const is not None:
            return ''
        return super().preamble_stmt(stmt)
                
    def get_function_signature(self):
        fnname = self.name
        args = ', '.join([t+' '+n for t, n in self.get_arg_types_and_names()])
        function_signature = 'function %(fnname)s(%(args)s) public'%locals()
        return function_signature

    def get_arg_types_and_names(self):
        const_to_type = None
        if self.operand_types:
            try:
                const_to_type = {c: self.operand_types[i]
                             for i, c in enumerate(self.sorted_consts)}
            except Exception:
                const_to_type = None
        if not const_to_type:
            const_to_type = self.inferred_const_to_type
        return [(const_to_type[c], self.const_to_name[c]) for c in self.sorted_consts]
        

#expr_opcodes = set(chain(*[cls.opcodes for cls in Stmt.__subclasses__()]))


scopes = {}
function_scopes = {}
contract_scope = ContractScope(function_scopes)

def init():
    rendering_stmts = {k : [] for k in in_function}
    rendering_stmts_variable_index = {}

    # initialize function scopes
    for k in functions:
        if k in public_functions:
            scope = PublicFunctionScope(k)
        else:
            scope = PrivateFunctionScope(k)
        function_scopes[scope.scope_id] = scope
        scopes[scope.scope_id] = scope

    # initialize control scopes
    for l in set(chain(*in_loop.values())):
        scope = LoopScope(l)
        scopes[scope.scope_id] = scope
    for l in if_then_else_head:
        scope = IfThenElseScope(l)
        scopes[scope.scope_id] = scope
    # initialize opcodes
    for k, body in tac_blocks.items():
        if k not in reachable:
            continue
        for s in body:
            if s in highlevel_op:
                op = highlevel_op[s]
                use = highlevel_use[s]
            else:
                op = tac_op[s]
                use = tac_use[s]
            vars = tac_def.get(s, [])
            # attach the right scope
            rendering_stmt = Stmt.from_opcode(
                Scope.from_ids(statement_scope[s]), s, vars, op, *use
            )
            rendering_stmts[k].append(rendering_stmt)
            for v in vars:
                rendering_stmts_variable_index[v] = rendering_stmt
    # carefully coordinate resolution
    for s in scopes.values():
        my_scope_id = scope_scope.get(s.scope_id, [])
        s.my_scope = Scope.from_ids(my_scope_id)
        s.my_scope.append_children(s)
        
    for stmts in rendering_stmts.values():
        for s in stmts:
            s.resolve_usages(rendering_stmts_variable_index)
    minimize_expression_complexity(list(chain(*rendering_stmts.values())))
    for s in scopes.values():
        s.resolve_scope(rendering_stmts_variable_index)
    for stmts in rendering_stmts.values():
        for s in stmts:
            s.rendered_operands



class CFG:
    ''' Computes CFG properties and also a block factory'''

    class Block:
        def __init__(self, b, key):
            assert isinstance(b, str)
            self.b = b
            self.key = key
    
        def prev_block(self):
            return {k for k,v in edges if v == self.b}
    
        def next_block(self):
            return {v for k,v in edges if k == self.b}

        def is_next_linear(self, block):
            if not isinstance(block, type(self)):
                return False
            return block.key - self.key == 1
        
        def next_concrete_block(self, start = None, ttl = 10):
            if start is None:
                start = self
            if ttl <= 1:
                return {start.b}
            next = start.next_block()
            res = set()
            for n in next:
                if all(tac_op[stmt] == 'JUMP' for stmt in tac_blocks[n]):
                    res |= self.next_concrete_block(cfg.get_block(n), ttl -1)
                else:
                    res.add(n)
            return res

            
        def __lt__(self, other):
            assert isinstance(other, type(self))
            return other.key > self.key
    
        def __gt__(self, other):
            assert isinstance(other, type(self))
            return other < self
    
        def __eq__(self, other):
            return self.b == other.b
    
        def __hash__(self):
            return hash(self.b) + 40

    def __init__(self):
        self.next_dict = defaultdict(set)
        for k, v in edges:
            self.next_dict[k].add(v)
        self.entries = set(function_entries)
        self.serialized_blocks = []
        self.distances = defaultdict(lambda : 0xFFFF)
        self.calculate_distances()
        for start in sorted(list(self.entries), key = sort_addresses_key):
            self.weighted_dfs(start)
        self.create_blocks()

    def statement_block(self, statement):
        block = None
        for b, stmts in tac_blocks.items():
            if statement in stmts:
                block = b
        if block == None:
            warning("None block for ", statement)
            return None
        return self.get_block(block)

    def calculate_distances(self):
        for entry in self.entries:
            self.recursive_min_distance(entry, 0)

    def recursive_min_distance(self, block, distance):
        old_distance = self.distances[block]
        if old_distance <= distance:
            return
        self.distances[block] = distance
        for next in self.next_dict[block]:
            self.recursive_min_distance(next, distance+1)

    def weighted_dfs(self, start):
        if start in self.serialized_blocks:
            return
        self.serialized_blocks.append(start)
        breadth_order = sorted(
            list(self.next_dict[start]),
            key = sort_addresses_key
        )
        for next in breadth_order:
            if self.distances[start] > self.distances[next]:
                continue
            self.weighted_dfs(next)

    def create_blocks(self):
        self.blocks = {b:self.Block(b, key) for key, b in enumerate(self.serialized_blocks)}
        
    def get_block(self, block):
        res = self.blocks.get(block)
        return res

cfg = CFG()

for fro, to in edges:
    # insert default placeholder items
    tac_blocks[fro] ; tac_blocks[to]

  
if __name__ == '__main__':
    try:
        init()
        rendered = contract_scope.render_all_statements()
        if args.development:
            print(rendered)
        with open('decompiled.sol', 'w') as f:
            f.write(rendered)
        abi = contract_scope.get_abi()
        with open('abi.json', 'w') as f:
            json.dump(abi, f)
        #debug = contract_scope.get_debug()
        #with open('debug.json', 'w') as f:
            #json.dump(debug, f)
    except Exception:
        extype, value, tb = sys.exc_info()
        traceback.print_exc()
        warning('Error decompiling results at:', os.getcwd())
        if args.development:
            pdb.post_mortem(tb)
