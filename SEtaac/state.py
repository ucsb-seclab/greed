import datetime
import logging

import z3

from collections import defaultdict

from SEtaac import utils
from SEtaac.exceptions import ExternalData, SymbolicError, IntractablePath, VMException
from SEtaac.memory import SymRead, SymbolicMemory
from SEtaac.storage import SymbolicStorage
from SEtaac.utils import concrete, is_true, get_solver, translate_xid


class AbstractEVMState(object):
    def __init__(self, code=None):
        self.code = code or bytearray()
        self.pc = 0
        self.memory = None
        self.trace = list()
        self.gas = None


class SymbolicEVMState(AbstractEVMState):
    def __init__(self, xid, program=None, code=None):
        super(SymbolicEVMState, self).__init__(code)
        self.program = program
        self.xid = xid

        self.memory = SymbolicMemory()
        self.storage = SymbolicStorage(self.xid)
        self.registers = defaultdict(None)

        self.instruction_count = 0
        self.halt = False
        self.error = None

        self.gas = z3.BitVec('GAS_%d' % self.xid, 256)
        self.start_balance = z3.BitVec('BALANCE_%d' % self.xid, 256)
        self.balance = self.start_balance
        self.balance += utils.ctx_or_symbolic('CALLVALUE', self.ctx, self.xid)

        self.ctx = dict()
        self.ctx['CODESIZE-ADDRESS'] = len(code)  # todo: code can be None

        self.constraints = list()
        self.sha_constraints = dict()

        # make sure we can exploit it in the foreseeable future
        self.min_timestamp = (datetime.datetime.now() - datetime.datetime(1970, 1, 1)).total_seconds()
        self.max_timestamp = (datetime.datetime(2020, 1, 1) - datetime.datetime(1970, 1, 1)).total_seconds()

        self.MAX_CALLDATA_SIZE = 256
        self.calldata = z3.Array('CALLDATA_%d' % self.xid, z3.BitVecSort(256), z3.BitVecSort(8))
        self.calldatasize = z3.BitVec('CALLDATASIZE_%d' % self.xid, 256)
        self.calldata_accesses = [0]

        self._handlers = {
            'ADD': self.add_handler,
            'SUB': self.sub_handler,
            'MUL': self.mul_handler,
            'DIV': self.div_handler,
            'MOD': self.mod_handler,
            'SDIV': self.sdiv_handler,
            'SMOD': self.smod_handler,
            'ADDMOD': self.addmod_handler,
            'MULMOD': self.mulmod_handler,
            'EXP': self.exp_handler,
            'SIGNEXTEND': self.signextend_handler,
            'LT': self.lt_handler,
            'GT': self.gt_handler,
            'SLT': self.slt_handler,
            'SGT': self.sgt_handler,
            'EQ': self.eq_handler,
            'ISZERO': self.iszero_handler,
            'AND': self.and_handler,
            'OR': self.or_handler,
            'XOR': self.xor_handler,
            'NOT': self.not_handler,
            'BYTE': self.byte_handler,
            'SHL': self.shl_handler,
            'SHR': self.shr_handler,
            'SAR': self.sar_handler,
            'SHA3': self.sha3_handler,
            'ADDRESS': self.address_handler,
            'BALANCE': self.balance_handler,
            'ORIGIN': self.origin_handler,
            'CALLER': self.caller_handler,
            'CALLVALUE': self.callvalue_handler,
            'CALLDATALOAD': self.calldataload_handler,
            'CALLDATASIZE': self.calldatasize_handler,
            'CALLDATACOPY': self.calldatacopy_handler,
            'CODESIZE': self.codesize_handler,
            'CODECOPY': self.codecopy_handler,
            'RETURNDATACOPY': self.returndatacopy_handler,
            'RETURNDATASIZE': self.returndatasize_handler,
            'GASPRICE': self.gasprice_handler,
            'EXTCODESIZE': self.extcodesize_handler,
            'EXTCODECOPY': self.extcodecopy_handler,
            'BLOCKHASH': self.blockhash_handler,
            'COINBASE': self.coinbase_handler,
            'TIMESTAMP': self.timestamp_handler,
            'NUMBER': self.number_handler,
            'DIFFICULTY': self.difficulty_handler,
            'GASLIMIT': self.gaslimit_handler,
            'MLOAD': self.mload_handler,
            'MSTORE': self.mstore_handler,
            'MSTORE8': self.mstore8_handler,
            'SLOAD': self.sload_handler,
            'SSTORE': self.sstore_handler,
            'JUMP': self.jump_handler,
            'JUMPI': self.jumpi_handler,
            'PC': self.pc_handler,
            'MSIZE': self.msize_handler,
            'GAS': self.gas_handler,
            'CREATE': self.create_handler,
            'CALL': self.call_handler,
            'CALLCODE': self.callcode_handler,
            'DELEGATECALL': self.delegatecall_handler,
            'STATICCALL': self.staticcall_handler,
            'RETURN': self.return_handler,
            'REVERT': self.revert_handler,
            'SELFDESTRUCT': self.selfdestruct_handler,
            'STOP': self.stop_handler,
        }

        self.handler_should_increment_pc = {
            h: (True if h not in ['JUMP', 'JUMPI'] else False)
            for h in self._handlers
        }


    @property
    def curr_stmt(self):
        # todo: pass project to state
        # todo: pc is the statement id
        return self.project.tac_parser.get_stmt_at(self.pc)

    @property
    def set_next_pc(self):
        # todo: read next statement from dict
        next_pcs = get_next_pcs(self.curr_stmt)
        assert len(next_pcs) == 1
        self.pc = next_pcs[0]

    def copy(self, new_xid):
        # todo: implement state copy
        new_state = SymbolicEVMState(new_xid, code=self.code)

        new_state.pc = self.pc
        self.memory = None
        self.trace = list()
        self.gas = None

        new_state.storage = self.storage.copy(new_xid)
        new_state.pc = self.pc
        new_state.trace = list(self.trace)
        new_state.start_balance = translate_xid(self.start_balance, new_xid)
        new_state.balance = translate_xid(self.balance, new_xid)

        new_state.constraints = list(self.constraints)
        new_state.sha_constraints = dict(self.sha_constraints)
        new_state.ctx = dict(self.ctx)

        return new_state

    def step(self):
        # todo: parse next instruction
        # todo: then execute correct handler and eventually assign return value to lhs

        self.trace.append(self.pc)
        self.instruction_count += 1

        ins = self.program[self.pc]
        self.gas -= ins.gas

        if ins.name in self._handlers:
            pass
            #self._handlers[ins.name]()  # todo: need to pass args here (can read ins.inputs to know how many)
        else:
            pass

        if self.handler_should_increment_pc[ins.name]:
            self.pc += 1

    # todo: assuming no side-effects in handlers, since in the evm they can only pop and then push new value (our return)

    # Arithmetic
    def add_handler(self, s0, s1):
        return s0 + s1

    def sub_handler(self, s0, s1):
        return s0 - s1

    def mul_handler(self, s0, s1):
        return s0 * s1

    def div_handler(self, s0, s1):
        if concrete(s1):
            return 0 if s1 == 0 else s0 / s1 if concrete(s0) else z3.UDiv(s0, s1)
        else:
            return z3.If(s1 == 0, z3.BitVecVal(0, 256), z3.UDiv(s0, s1))

    def mod_handler(self, s0, s1):
        if concrete(s1):
            return 0 if s1 == 0 else s0 % s1
        else:
            return z3.If(s1 == 0, z3.BitVecVal(0, 256), z3.URem(s0, s1))

    def sdiv_handler(self, s0, s1):
        if concrete(s0) and concrete(s1):
            s0, s1 = utils.to_signed(s0), utils.to_signed(s1)
            return 0 if s1 == 0 else abs(s0) // abs(s1) * (-1 if s0 * s1 < 0 else 1)
        elif concrete(s1):
            return 0 if s1 == 0 else s0 / s1
        else:
            return z3.If(s1 == 0, z3.BitVecVal(0, 256), s0 / s1)

    def smod_handler(self, s0, s1):
        if concrete(s0) and concrete(s1):
            s0, s1 = utils.to_signed(s0), utils.to_signed(s1)
            return 0 if s1 == 0 else abs(s0) % abs(s1) * (-1 if s0 < 0 else 1)
        elif concrete(s1):
            return 0 if s1 == 0 else z3.SRem(s0, s1)
        else:
            return z3.If(s1 == 0, z3.BitVecVal(0, 256), z3.SRem(s0, s1))

    def addmod_handler(self, s0, s1, s2):
        if concrete(s2):
            return (s0 + s1) % s2 if s2 else 0
        else:
            return z3.If(s2 == 0, z3.BitVecVal(0, 256), z3.URem((s0 + s1), s2))

    def mulmod_handler(self, s0, s1, s2):
        if concrete(s2):
            return (s0 * s1) % s2 if s2 else 0
        else:
            return z3.If(s2 == 0, z3.BitVecVal(0, 256), z3.URem((s0 * s1), s2))

    def exp_handler(self, base, exponent):
        if concrete(base) and concrete(exponent):
            return pow(base, exponent, utils.TT256)
        else:
            if concrete(base) and utils.is_pow2(base):
                l2 = utils.log2(base)
                return 1 << (l2 * exponent)
            else:
                raise SymbolicError('exponentiation with symbolic exponent currently not supported :-/')

    def signextend_handler(self, s0, s1):
        if concrete(s0) and concrete(s1):
            if s0 <= 31:
                testbit = s0 * 8 + 7
                if s1 & (1 << testbit):
                    return s1 | (utils.TT256 - (1 << testbit))
                else:
                    return s1 & ((1 << testbit) - 1)
            else:
                return s1
        elif concrete(s0):
            if s0 <= 31:
                oldwidth = (s0 + 1) * 8
                return z3.SignExt(256 - oldwidth, s1)
            else:
                return s1
        else:
            raise SymbolicError('symbolic bitwidth for signextension is currently not supported')

    # Comparisons
    def lt_handler(self, s0, s1):
        if concrete(s0) and concrete(s1):
            return 1 if s0 < s1 else 0
        else:
            return z3.If(z3.ULT(s0, s1), z3.BitVecVal(1, 256), z3.BitVecVal(0, 256))

    def gt_handler(self, s0, s1):
        if concrete(s0) and concrete(s1):
            return 1 if s0 > s1 else 0
        else:
            return z3.If(z3.UGT(s0, s1), z3.BitVecVal(1, 256), z3.BitVecVal(0, 256))

    def slt_handler(self, s0, s1):
        if concrete(s0) and concrete(s1):
            s0, s1 = utils.to_signed(s0), utils.to_signed(s1)
            return 1 if s0 < s1 else 0
        else:
            return z3.If(s0 < s1, z3.BitVecVal(1, 256), z3.BitVecVal(0, 256))

    def sgt_handler(self, s0, s1):
        if concrete(s0) and concrete(s1):
            s0, s1 = utils.to_signed(s0), utils.to_signed(s1)
            return 1 if s0 > s1 else 0
        else:
            return z3.If(s0 > s1, z3.BitVecVal(1, 256), z3.BitVecVal(0, 256))

    def eq_handler(self, s0, s1):
        if concrete(s0) and concrete(s1):
            return 1 if s0 == s1 else 0
        else:
            return z3.If(s0 == s1, z3.BitVecVal(1, 256), z3.BitVecVal(0, 256))

    def iszero_handler(self, s0):
        if concrete(s0):
            return 1 if s0 == 0 else 0
        else:
            return z3.If(s0 == 0, z3.BitVecVal(1, 256), z3.BitVecVal(0, 256))

    def and_handler(self, s0, s1):
        return s0 & s1

    def or_handler(self, s0, s1):
        return s0 | s1

    def xor_handler(self, s0, s1):
        return s0 ^ s1

    def not_handler(self, s0):
        return ~s0

    def byte_handler(self, s0, s1):
        if concrete(s0):
            if s0 >= 32:
                return 0
            else:
                if concrete(s1):
                    return (s1 // 256 ** (31 - s0)) % 256
                else:
                    v = z3.simplify(z3.Extract((31 - s0) * 8 + 7, (31 - s0) * 8, s1))
                    if z3.is_bv_value(v):
                        return v.as_long()
                    else:
                        return z3.ZeroExt(256 - 32, v)
        else:
            raise SymbolicError('symbolic byte-index not supported')

    def shl_handler(self, s0, s1):
        return s1 << s0

    def shr_handler(self, s0, s1):
        if concrete(s1) and concrete(s0):
            return s1 >> s0
        else:
            return z3.LShR(s1, s0)

    def sar_handler(self, s0, s1):
        return utils.to_signed(s1) >> s0

    # SHA3 and environment info
    def sha3_handler(self, s0, s1):
        self.memory.extend(s0, s1)
        mm = self.memory.read(s0, s1)
        if not isinstance(mm, SymRead) and all(concrete(m) for m in mm):
            data = utils.bytearray_to_bytestr(mm)
            return utils.big_endian_to_int(utils.sha3(data))
        else:
            if not isinstance(mm, SymRead):
                sha_data = z3.simplify(z3.Concat([m if z3.is_expr(m) else z3.BitVecVal(m, 8) for m in mm]))
                for k, v in self.sha_constraints.items():
                    if isinstance(v, SymRead):
                        continue
                    if v.size() == sha_data.size() and is_true(v == sha_data):
                        sha = k
                        break
                else:
                    sha = z3.BitVec('SHA3_%x_%d' % (self.instruction_count, self.xid), 256)
                    self.sha_constraints[sha] = sha_data
            else:
                sha_data = mm
                sha = z3.BitVec('SHA3_%x_%d' % (self.instruction_count, self.xid), 256)
                self.sha_constraints[sha] = sha_data
            return sha
            # raise SymbolicError('symbolic computation of SHA3 not supported')

    def address_handler(self, ):
        return utils.ctx_or_symbolic('ADDRESS', self.ctx, self.xid)

    def balance_handler(self, s0):
        if concrete(s0):
            return utils.ctx_or_symbolic('BALANCE-%x' % s0, self.ctx, self.xid)
        elif is_true(utils.addr(s0) == utils.addr(utils.ctx_or_symbolic('ADDRESS', self.ctx, self.xid))):
            return self.balance
        elif is_true(utils.addr(s0) == utils.addr(utils.ctx_or_symbolic('ORIGIN', self.ctx, self.xid))):
            return utils.ctx_or_symbolic('BALANCE-ORIGIN', self.ctx, self.xid)
        elif is_true(utils.addr(s0) == utils.addr(utils.ctx_or_symbolic('CALLER', self.ctx, self.xid))):
            return utils.ctx_or_symbolic('BALANCE-CALLER', self.ctx, self.xid)
        else:
            raise SymbolicError('balance of symbolic address (%s)' % str(z3.simplify(s0)))

    def origin_handler(self, ):
        return utils.ctx_or_symbolic('ORIGIN', self.ctx, self.xid)

    def caller_handler(self, ):
        return utils.ctx_or_symbolic('CALLER', self.ctx, self.xid)

    def callvalue_handler(self, ):
        return utils.ctx_or_symbolic('CALLVALUE', self.ctx, self.xid)

    def calldataload_handler(self, s0):
        self.constraints.append(z3.UGE(self.calldatasize, s0 + 32))
        self.calldata_accesses.append(s0 + 32)
        if not concrete(s0):
            self.constraints.append(z3.ULT(s0, self.MAX_CALLDATA_SIZE))
        return z3.Concat([self.calldata[s0 + i] for i in range(32)])

    def calldatasize_handler(self, ):
        return self.calldatasize

    def calldatacopy_handler(self, mstart, dstart, size):
        self.constraints.append(z3.UGE(self.calldatasize, dstart + size))
        self.calldata_accesses.append(dstart + size)
        if not concrete(dstart):
            self.constraints.append(z3.ULT(dstart, self.MAX_CALLDATA_SIZE))
        if concrete(size):
            for i in range(size):
                self.memory[mstart + i] = self.calldata[dstart + i]
        else:
            self.constraints.append(z3.ULT(size, self.MAX_CALLDATA_SIZE))
            for i in range(self.MAX_CALLDATA_SIZE):
                self.memory[mstart + i] = z3.If(size < i, self.memory[mstart + i], self.calldata[dstart + i])

    def codesize_handler(self, ):
        return len(self.code)

    def codecopy_handler(self, mstart, dstart, size):
        if concrete(mstart) and concrete(dstart) and concrete(size):
            self.memory.extend(mstart, size)
            for i in range(size):
                if dstart + i < len(self.code):
                    self.memory[mstart + i] = self.code[dstart + i]
                else:
                    self.memory[mstart + i] = 0
        else:
            raise SymbolicError('Symbolic code index @ %s' % self.pc)

    def returndatacopy_handler(self, ):
        raise ExternalData('RETURNDATACOPY')

    def returndatasize_handler(self, ):
        raise ExternalData('RETURNDATASIZE')

    def gasprice_handler(self, ):
        return utils.ctx_or_symbolic('GASPRICE', self.ctx, self.xid)

    def extcodesize_handler(self, s0):
        if concrete(s0):
            return utils.ctx_or_symbolic('CODESIZE-%x' % s0, self.ctx, self.xid)
        elif is_true(s0 == utils.addr(utils.ctx_or_symbolic('ADDRESS', self.ctx, self.xid))):
            return utils.ctx_or_symbolic('CODESIZE-ADDRESS', self.ctx, self.xid)
        elif is_true(s0 == utils.addr(utils.ctx_or_symbolic('CALLER', self.ctx, self.xid))):
            return utils.ctx_or_symbolic('CODESIZE-CALLER', self.ctx, self.xid)
        else:
            raise SymbolicError('codesize of symblic address')

    def extcodecopy_handler(self, ):
        raise ExternalData('EXTCODECOPY')

    # Block info
    def blockhash_handler(self, s0):
        if not concrete(s0):
            raise SymbolicError('symbolic blockhash index')
        return utils.ctx_or_symbolic('BLOCKHASH[%d]' % s0, self.ctx, self.xid)

    def coinbase_handler(self, ):
        return utils.ctx_or_symbolic('COINBASE', self.ctx, self.xid)

    def timestamp_handler(self, ):
        ts = utils.ctx_or_symbolic('TIMESTAMP', self.ctx, self.xid)
        if not concrete(ts):
            self.constraints.append(z3.UGE(ts, self.min_timestamp))
            self.constraints.append(z3.ULE(ts, self.max_timestamp))
        return ts

    def number_handler(self, ):
        return utils.ctx_or_symbolic('NUMBER', self.ctx, self.xid)

    def difficulty_handler(self, ):
        return utils.ctx_or_symbolic('DIFFICULTY', self.ctx, self.xid)

    def gaslimit_handler(self, ):
        return utils.ctx_or_symbolic('GASLIMIT', self.ctx, self.xid)

    # VM state manipulations
    def mload_handler(self, s0):
        self.memory.extend(s0, 32)
        mm = [self.memory[s0 + i] for i in range(32)]
        if all(concrete(m) for m in mm):
            return utils.bytes_to_int(self.memory.read(s0, 32))
        else:
            v = z3.simplify(z3.Concat([m if not concrete(m) else z3.BitVecVal(m, 8) for m in mm]))
            if z3.is_bv_value(v):
                return v.as_long()
            else:
                return v

    def mstore_handler(self, s0, s1):
        self.memory.extend(s0, 32)
        if concrete(s1):
            self.memory.write(s0, 32, utils.encode_int32(s1))
        else:
            for i in range(32):
                m = z3.simplify(z3.Extract((31 - i) * 8 + 7, (31 - i) * 8, s1))
                if z3.is_bv_value(m):
                    self.memory[s0 + i] = m.as_long()
                else:
                    self.memory[s0 + i] = m

    def mstore8_handler(self, s0, s1):
        self.memory.extend(s0, 1)
        self.memory[s0] = s1 % 256

    def sload_handler(self, s0):
        v = z3.simplify(self.storage[s0])
        if z3.is_bv_value(v):
            return v.as_long()
        else:
            return v

    def sstore_handler(self, s0, s1):
        self.storage[s0] = s1

    def pc_handler(self, ):
        return self.pc

    def msize_handler(self, ):
        return len(self.memory)

    def gas_handler(self, ):
        return z3.BitVec('GAS_%x' % self.instruction_count, 256)

    # Logs (aka "events")
    # todo: implement logs
    # elif op[:3] == 'LOG':
    #     """
    #     0xa0 ... 0xa4, 32/64/96/128/160 + len(data) gas
    #     a. Opcodes LOG0...LOG4 are added, takes 2-6 stack arguments
    #             MEMSTART MEMSZ (TOPIC1) (TOPIC2) (TOPIC3) (TOPIC4)
    #     b. Logs are kept track of during tx execution exactly the same way as selfdestructs
    #        (except as an ordered list, not a set).
    #        Each log is in the form [address, [topic1, ... ], data] where:
    #        * address is what the ADDRESS opcode would output
    #        * data is self.memory[MEMSTART: MEMSTART + MEMSZ]
    #        * topics are as provided by the opcode
    #     c. The ordered list of logs in the transaction are expressed as [log0, log1, ..., logN].
    #     """
    #     depth = int(op[3:])
    #     mstart, msz = stk.pop(), stk.pop()
    #     topics = [stk.pop() for _ in range(depth)]
    #     self.memory.extend(mstart, msz)
    #     # Ignore external effects...

    # Create a new contract
    def create_handler(self, s0, s1, s2):
        self.constraints.append(z3.UGE(self.balance, s0))
        self.balance -= s0
        return utils.addr(z3.BitVec('EXT_CREATE_%d_%d' % (self.instruction_count, self.xid), 256))

    # Calls
    def _call_handler(self, s0, s1, s2, s3, s4, s5, s6):
        ostart = s5 if concrete(s5) else z3.simplify(s5)
        olen = s6 if concrete(s6) else z3.simplify(s6)

        if concrete(s1) and s1 <= 8:
            if s1 == 4:
                logging.info("Calling precompiled identity contract")
                istart = s3 if concrete(s3) else z3.simplify(s3)
                ilen = s4 if concrete(s4) else z3.simplify(s4)
                self.memory.copy(istart, ilen, ostart, olen)
                return 1
            else:
                raise SymbolicError("Precompiled contract %d not implemented" % s1)
        else:
            for i in range(olen):
                self.memory[ostart + i] = z3.BitVec('EXT_%d_%d_%d' % (self.instruction_count, i, self.xid), 8)
            logging.info("Calling contract %s (%d_%d)" % (s1, self.instruction_count, self.xid))
            return z3.BitVec('CALLRESULT_%d_%d' % (self.instruction_count, self.xid), 256)

    def call_handler(self, s0, s1, s2, s3, s4, s5, s6):
        self.constraints.append(z3.UGE(self.balance, s2))
        self.balance -= s2
        return self._call_handler(s0, s1, s2, s3, s4, s5, s6)

    def callcode_handler(self, s0, s1, s2, s3, s4, s5, s6):
        return self._call_handler(s0, s1, s2, s3, s4, s5, s6)

    def delegatecall_handler(self, s0, s1, s3, s4, s5, s6):
        s2 = utils.ctx_or_symbolic('CALLVALUE', self.ctx, self.xid)
        return self._call_handler(s0, s1, s2, s3, s4, s5, s6)

    def staticcall_handler(self, s0, s1, s3, s4, s5, s6):
        s2 = 0
        return self._call_handler(s0, s1, s2, s3, s4, s5, s6)

    # Terminate
    def return_handler(self, s0, s1):
        if concrete(s0) and concrete(s1):
            self.memory.extend(s0, s1)
        self.constraints.append(z3.Or(*(z3.ULE(self.calldatasize, access) for access in self.calldata_accesses)))
        self.halt = True

    def revert_handler(self, s0, s1):
        if not concrete(s0) or not concrete(s1):
            raise SymbolicError('symbolic memory index')
        self.memory.extend(s0, s1)
        self.constraints.append(z3.Or(*(z3.ULE(self.calldatasize, access) for access in self.calldata_accesses)))
        self.halt = True

    def selfdestruct_handler(self, s0):
        self.constraints.append(z3.Or(*(z3.ULE(self.calldatasize, access) for access in self.calldata_accesses)))
        self.halt = True

    def stop_handler(self, ):
        self.constraints.append(z3.Or(*(z3.ULE(self.calldatasize, access) for access in self.calldata_accesses)))
        self.halt = True
