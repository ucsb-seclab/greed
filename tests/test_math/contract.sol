pragma solidity 0.8.7;

contract TestMath {
    event Event(string message);

    function log(string memory message) private {
        //emit Event(message);
        assembly {
            // manually emit a technically invalid LOG1 that we
            // can then recognize and parse in the testing routine
            log1(0x0, 0x0, message)
        }
    }

    function add(uint a, uint b) private pure returns (uint result) {
        assembly {
            result := add(a, b)
        }
    }

    function sub(uint a, uint b) private pure returns (uint result) {
        assembly {
            result := sub(a, b)
        }
    }

    function mul(uint a, uint b) private pure returns (uint result) {
        assembly {
            result := mul(a, b)
        }
    }

    function div(uint a, uint b) private pure returns (uint result) {
        assembly {
            result := div(a, b)
        }
    }

    function sdiv(uint a, uint b) private pure returns (uint result) {
        assembly {
            result := sdiv(a, b)
        }
    }

    function mod(uint a, uint b) private pure returns (uint result) {
        assembly {
            result := mod(a, b)
        }
    }

    function smod(uint a, uint b) private pure returns (uint result) {
        assembly {
            result := smod(a, b)
        }
    }

    function addmod(uint a, uint b, uint n) private pure returns (uint result) {
        assembly {
            result := addmod(a, b, n)
        }
    }

    function mulmod(uint a, uint b, uint n) private pure returns (uint result) {
        assembly {
            result := mulmod(a, b, n)
        }
    }

    function exp(uint a, uint exponent) private pure returns (uint result) {
        assembly {
            result := exp(a, exponent)
        }
    }

    function signextend(uint a, uint x) private pure returns (uint result) {
        assembly {
            result := signextend(a, x)
        }
    }

    function lt(uint a, uint b) private pure returns (uint result) {
        assembly {
            result := lt(a, b)
        }
    }

    function gt(uint a, uint b) private pure returns (uint result) {
        assembly {
            result := gt(a, b)
        }
    }

    function slt(uint a, uint b) private pure returns (uint result) {
        assembly {
            result := slt(a, b)
        }
    }

    function sgt(uint a, uint b) private pure returns (uint result) {
        assembly {
            result := sgt(a, b)
        }
    }

    function eq(uint a, uint b) private pure returns (uint result) {
        assembly {
            result := eq(a, b)
        }
    }

    function iszero(uint a) private pure returns (uint result) {
        assembly {
            result := iszero(a)
        }
    }

    function and(uint a, uint b) private pure returns (uint result) {
        assembly {
            result := and(a, b)
        }
    }

    function or(uint a, uint b) private pure returns (uint result) {
        assembly {
            result := or(a, b)
        }
    }

    function xor(uint a, uint b) private pure returns (uint result) {
        assembly {
            result := xor(a, b)
        }
    }

    function not(uint a) private pure returns (uint result) {
        assembly {
            result := not(a)
        }
    }

    function byte_(uint i, uint x) private pure returns (uint result) {
        assembly {
            result := byte(i, x)
        }
    }

    function shl(uint a, uint b) private pure returns (uint result) {
        assembly {
            result := shl(a, b)
        }
    }

    function shr(uint a, uint b) private pure returns (uint result) {
        assembly {
            result := shr(a, b)
        }
    }

    function sar(uint a, uint b) private pure returns (uint result) {
        assembly {
            result := sar(a, b)
        }
    }

    fallback() external {

        if (add(10, 10) != 20) {
            log("error:test_add");
            revert();
        }
        log("success:test_add");

        if (add(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF, 1) != 0) {
            log("error:test_add_overflow");
            revert();
        }
        log("success:test_add_overflow");

        if (sub(10, 10) != 0) {
            log("error:test_sub");
            revert();
        }
        log("success:test_sub");

        if (sub(0, 1) != 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF) {
            log("error:test_sub_overflow");
            revert();
        }
        log("success:test_sub_overflow");

        if (mul(10, 10) != 100) {
            log("error:test_mul");
            revert();
        }
        log("success:test_mul");

        if (mul(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF, 2) != 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE) {
            log("error:test_mul_overflow");
            revert();
        }
        log("success:test_mul_overflow");

        if (div(10, 10) != 1) {
            log("error:test_div");
            revert();
        }
        log("success:test_div");

        if (div(10, 0) != 0) {
            log("error:test_div_0");
            revert();
        }
        log("success:test_div_0");

        if (div(1, 2) != 0) {
            log("error:test_div_lt");
            revert();
        }
        log("success:test_div_lt");

        if (div(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE, 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF) != 0) {
            log("error:test_div_signed");
            revert();
        }
        log("success:test_div_signed");

        if (sdiv(10, 10) != 1) {
            log("error:test_sdiv_1");
            revert();
        }
        log("success:test_sdiv_1");

        if (sdiv(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE, 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF) != 2) {
            log("error:test_sdiv_signed");
            revert();
        }
        log("success:test_sdiv_signed");

        if (mod(10, 3) != 1) {
            log("error:test_mod_3");
            revert();
        }
        log("success:test_mod_3");

        if (mod(17, 5) != 2) {
            log("error:test_mod_5");
            revert();
        }
        log("success:test_mod_5");

        if (smod(10, 3) != 1) {
            log("error:test_smod_3");
            revert();
        }
        log("success:test_smod_3");

        if (smod(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF8, 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFD) != 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE) {
            log("error:test_smod_signed");
            revert();
        }
        log("success:test_smod_signed");

        if (addmod(10, 10, 8) != 4) {
            log("error:test_addmod");
            revert();
        }
        log("success:test_addmod");

        if (addmod(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF, 2, 2) != 1) {
            log("error:test_addmod_overflow");
            revert();
        }
        log("success:test_addmod_overflow");

        if (mulmod(10, 10, 8) != 4) {
            log("error:test_mulmod");
            revert();
        }
        log("success:test_mulmod");

        if (mulmod(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF, 12) != 9) {
            log("error:test_mulmod_overflow");
            revert();
        }
        log("success:test_mulmod_overflow");

        if (exp(10, 2) != 100) {
            log("error:test_exp_10");
            revert();
        }
        log("success:test_exp_10");

        if (exp(2, 2) != 4) {
            log("error:test_exp_2");
            revert();
        }
        log("success:test_exp_2");

        if (signextend(0, 0xff) != 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF) {
            log("error:test_signextend_ff");
            revert();
        }
        log("success:test_signextend_ff");

        if (signextend(0, 0x7f) != 0x7f) {
            log("error:test_signextend_7f");
            revert();
        }
        log("success:test_signextend_7f");

        if (lt(9, 10) != 1) {
            log("error:test_lt_9");
            revert();
        }
        log("success:test_lt_9");

        if (lt(10, 10) != 0) {
            log("error:test_lt_10");
            revert();
        }
        log("success:test_lt_10");

        if (lt(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF, 0) != 0) {
            log("error:test_lt_signed");
            revert();
        }
        log("success:test_lt_signed");

        if (gt(10, 9) != 1) {
            log("error:test_gt_9");
            revert();
        }
        log("success:test_gt_9");

        if (gt(10, 10) != 0) {
            log("error:test_gt_10");
            revert();
        }
        log("success:test_gt_10");

        if (gt(0, 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF) != 0) {
            log("error:test_gt_signed");
            revert();
        }
        log("success:test_gt_signed");

        if (slt(10, 10) != 0) {
            log("error:test_slt_10");
            revert();
        }
        log("success:test_slt_10");

        if (slt(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF, 0) != 1) {
            log("error:test_slt_signed");
            revert();
        }
        log("success:test_slt_signed");

        if (sgt(10, 10) != 0) {
            log("error:test_sgt_10");
            revert();
        }
        log("success:test_sgt_10");

        if (sgt(0, 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF) != 1) {
            log("error:test_sgt_signed");
            revert();
        }
        log("success:test_sgt_signed");

        if (eq(10, 10) != 1) {
            log("error:test_eq_10");
            revert();
        }
        log("success:test_eq_10");

        if (eq(10, 5) != 0) {
            log("error:test_eq_5");
            revert();
        }
        log("success:test_eq_5");

        if (iszero(10) != 0) {
            log("error:test_iszero_10");
            revert();
        }
        log("success:test_iszero_10");

        if (iszero(0) != 1) {
            log("error:test_iszero_0");
            revert();
        }
        log("success:test_iszero_0");

        if (and(0xF, 0xF) != 0xF) {
            log("error:test_and_0xF");
            revert();
        }
        log("success:test_and_0xF");

        if (and(0xFF, 0) != 0) {
            log("error:test_and_0");
            revert();
        }
        log("success:test_and_0");

        if (or(0xF0, 0xF) != 0xFF) {
            log("error:test_or_F0");
            revert();
        }
        log("success:test_or_F0");

        if (or(0xFF, 0xFF) != 0xFF) {
            log("error:test_or_FF");
            revert();
        }
        log("success:test_or_FF");

        if (xor(0xF0, 0xF) != 0xFF) {
            log("error:test_xor_F0");
            revert();
        }
        log("success:test_xor_F0");

        if (xor(0xFF, 0xFF) != 0) {
            log("error:test_xor_FF");
            revert();
        }
        log("success:test_xor_FF");

        if (not(0) != 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF) {
            log("error:test_not_0");
            revert();
        }
        log("success:test_not_0");

        if (byte_(31, 0xFF) != 0xFF) {
            log("error:testbyte_31");
            revert();
        }
        log("success:testbyte_31");

        if (byte_(30, 0xFF00) != 0xFF) {
            log("error:testbyte_30");
            revert();
        }
        log("success:testbyte_30");

        if (shl(1, 1) != 2) {
            log("error:testshl_1");
            revert();
        }
        log("success:testshl_1");

        if (shl(4, 0xFF00000000000000000000000000000000000000000000000000000000000000) != 0xF000000000000000000000000000000000000000000000000000000000000000) {
            log("error:testshl_FF");
            revert();
        }
        log("success:testshl_FF");

        if (shr(1, 2) != 1) {
            log("error:testshr_1");
            revert();
        }
        log("success:testshr_1");

        if (shr(4, 0xFF) != 0xF) {
            log("error:testshr_FF");
            revert();
        }
        log("success:testshr_FF");

        if (sar(1, 2) != 1) {
            log("error:testsar_1");
            revert();
        }
        log("success:testsar_1");

        if (sar(4, 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF0) != 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF) {
            log("error:testsar_FF");
            revert();
        }
        log("success:testsar_FF");


        log("success:");
    }
}
