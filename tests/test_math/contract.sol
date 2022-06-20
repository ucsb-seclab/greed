pragma solidity 0.8.7;

contract TestMath {

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
            assembly {log1(0, 0, "error:test_add")}
            revert();
        }
        assembly {log1(0, 0, "success:test_add")}

        if (add(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF, 1) != 0) {
            assembly {log1(0, 0, "error:test_add_overflow")}
            revert();
        }
        assembly {log1(0, 0, "success:test_add_overflow")}

        if (sub(10, 10) != 0) {
            assembly {log1(0, 0, "error:test_sub")}
            revert();
        }
        assembly {log1(0, 0, "success:test_sub")}

        if (sub(0, 1) != 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF) {
            assembly {log1(0, 0, "error:test_sub_overflow")}
            revert();
        }
        assembly {log1(0, 0, "success:test_sub_overflow")}

        if (mul(10, 10) != 100) {
            assembly {log1(0, 0, "error:test_mul")}
            revert();
        }
        assembly {log1(0, 0, "success:test_mul")}

        if (mul(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF, 2) != 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE) {
            assembly {log1(0, 0, "error:test_mul_overflow")}
            revert();
        }
        assembly {log1(0, 0, "success:test_mul_overflow")}

        if (div(10, 10) != 1) {
            assembly {log1(0, 0, "error:test_div")}
            revert();
        }
        assembly {log1(0, 0, "success:test_div")}

        if (div(10, 0) != 0) {
            assembly {log1(0, 0, "error:test_div_0")}
            revert();
        }
        assembly {log1(0, 0, "success:test_div_0")}

        if (div(1, 2) != 0) {
            assembly {log1(0, 0, "error:test_div_lt")}
            revert();
        }
        assembly {log1(0, 0, "success:test_div_lt")}

        if (div(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE, 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF) != 0) {
            assembly {log1(0, 0, "error:test_div_signed")}
            revert();
        }
        assembly {log1(0, 0, "success:test_div_signed")}

        if (sdiv(10, 10) != 1) {
            assembly {log1(0, 0, "error:test_sdiv_1")}
            revert();
        }
        assembly {log1(0, 0, "success:test_sdiv_1")}

        if (sdiv(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE, 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF) != 2) {
            assembly {log1(0, 0, "error:test_sdiv_signed")}
            revert();
        }
        assembly {log1(0, 0, "success:test_sdiv_signed")}

        if (mod(10, 3) != 1) {
            assembly {log1(0, 0, "error:test_mod_3")}
            revert();
        }
        assembly {log1(0, 0, "success:test_mod_3")}

        if (mod(17, 5) != 2) {
            assembly {log1(0, 0, "error:test_mod_5")}
            revert();
        }
        assembly {log1(0, 0, "success:test_mod_5")}

        if (smod(10, 3) != 1) {
            assembly {log1(0, 0, "error:test_smod_3")}
            revert();
        }
        assembly {log1(0, 0, "success:test_smod_3")}

        if (smod(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF8, 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFD) != 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE) {
            assembly {log1(0, 0, "error:test_smod_signed")}
            revert();
        }
        assembly {log1(0, 0, "success:test_smod_signed")}

        if (addmod(10, 10, 8) != 4) {
            assembly {log1(0, 0, "error:test_addmod")}
            revert();
        }
        assembly {log1(0, 0, "success:test_addmod")}

        if (addmod(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF, 2, 2) != 1) {
            assembly {log1(0, 0, "error:test_addmod_overflow")}
            revert();
        }
        assembly {log1(0, 0, "success:test_addmod_overflow")}

        if (mulmod(10, 10, 8) != 4) {
            assembly {log1(0, 0, "error:test_mulmod")}
            revert();
        }
        assembly {log1(0, 0, "success:test_mulmod")}

        if (mulmod(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF, 12) != 9) {
            assembly {log1(0, 0, "error:test_mulmod_overflow")}
            revert();
        }
        assembly {log1(0, 0, "success:test_mulmod_overflow")}

        if (exp(10, 2) != 100) {
            assembly {log1(0, 0, "error:test_exp_10")}
            revert();
        }
        assembly {log1(0, 0, "success:test_exp_10")}

        if (exp(2, 2) != 4) {
            assembly {log1(0, 0, "error:test_exp_2")}
            revert();
        }
        assembly {log1(0, 0, "success:test_exp_2")}

        if (signextend(0, 0xff) != 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF) {
            assembly {log1(0, 0, "error:test_signextend_ff")}
            revert();
        }
        assembly {log1(0, 0, "success:test_signextend_ff")}

        if (signextend(0, 0x7f) != 0x7f) {
            assembly {log1(0, 0, "error:test_signextend_7f")}
            revert();
        }
        assembly {log1(0, 0, "success:test_signextend_7f")}

        if (lt(9, 10) != 1) {
            assembly {log1(0, 0, "error:test_lt_9")}
            revert();
        }
        assembly {log1(0, 0, "success:test_lt_9")}

        if (lt(10, 10) != 0) {
            assembly {log1(0, 0, "error:test_lt_10")}
            revert();
        }
        assembly {log1(0, 0, "success:test_lt_10")}

        if (lt(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF, 0) != 0) {
            assembly {log1(0, 0, "error:test_lt_signed")}
            revert();
        }
        assembly {log1(0, 0, "success:test_lt_signed")}

        if (gt(10, 9) != 1) {
            assembly {log1(0, 0, "error:test_gt_9")}
            revert();
        }
        assembly {log1(0, 0, "success:test_gt_9")}

        if (gt(10, 10) != 0) {
            assembly {log1(0, 0, "error:test_gt_10")}
            revert();
        }
        assembly {log1(0, 0, "success:test_gt_10")}

        if (gt(0, 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF) != 0) {
            assembly {log1(0, 0, "error:test_gt_signed")}
            revert();
        }
        assembly {log1(0, 0, "success:test_gt_signed")}

        if (slt(10, 10) != 0) {
            assembly {log1(0, 0, "error:test_slt_10")}
            revert();
        }
        assembly {log1(0, 0, "success:test_slt_10")}

        if (slt(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF, 0) != 1) {
            assembly {log1(0, 0, "error:test_slt_signed")}
            revert();
        }
        assembly {log1(0, 0, "success:test_slt_signed")}

        if (sgt(10, 10) != 0) {
            assembly {log1(0, 0, "error:test_sgt_10")}
            revert();
        }
        assembly {log1(0, 0, "success:test_sgt_10")}

        if (sgt(0, 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF) != 1) {
            assembly {log1(0, 0, "error:test_sgt_signed")}
            revert();
        }
        assembly {log1(0, 0, "success:test_sgt_signed")}

        if (eq(10, 10) != 1) {
            assembly {log1(0, 0, "error:test_eq_10")}
            revert();
        }
        assembly {log1(0, 0, "success:test_eq_10")}

        if (eq(10, 5) != 0) {
            assembly {log1(0, 0, "error:test_eq_5")}
            revert();
        }
        assembly {log1(0, 0, "success:test_eq_5")}

        if (iszero(10) != 0) {
            assembly {log1(0, 0, "error:test_iszero_10")}
            revert();
        }
        assembly {log1(0, 0, "success:test_iszero_10")}

        if (iszero(0) != 1) {
            assembly {log1(0, 0, "error:test_iszero_0")}
            revert();
        }
        assembly {log1(0, 0, "success:test_iszero_0")}

        if (and(0xF, 0xF) != 0xF) {
            assembly {log1(0, 0, "error:test_and_0xF")}
            revert();
        }
        assembly {log1(0, 0, "success:test_and_0xF")}

        if (and(0xFF, 0) != 0) {
            assembly {log1(0, 0, "error:test_and_0")}
            revert();
        }
        assembly {log1(0, 0, "success:test_and_0")}

        if (or(0xF0, 0xF) != 0xFF) {
            assembly {log1(0, 0, "error:test_or_F0")}
            revert();
        }
        assembly {log1(0, 0, "success:test_or_F0")}

        if (or(0xFF, 0xFF) != 0xFF) {
            assembly {log1(0, 0, "error:test_or_FF")}
            revert();
        }
        assembly {log1(0, 0, "success:test_or_FF")}

        if (xor(0xF0, 0xF) != 0xFF) {
            assembly {log1(0, 0, "error:test_xor_F0")}
            revert();
        }
        assembly {log1(0, 0, "success:test_xor_F0")}

        if (xor(0xFF, 0xFF) != 0) {
            assembly {log1(0, 0, "error:test_xor_FF")}
            revert();
        }
        assembly {log1(0, 0, "success:test_xor_FF")}

        if (not(0) != 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF) {
            assembly {log1(0, 0, "error:test_not_0")}
            revert();
        }
        assembly {log1(0, 0, "success:test_not_0")}

        if (byte_(31, 0xFF) != 0xFF) {
            assembly {log1(0, 0, "error:testbyte_31")}
            revert();
        }
        assembly {log1(0, 0, "success:testbyte_31")}

        if (byte_(30, 0xFF00) != 0xFF) {
            assembly {log1(0, 0, "error:testbyte_30")}
            revert();
        }
        assembly {log1(0, 0, "success:testbyte_30")}

        if (shl(1, 1) != 2) {
            assembly {log1(0, 0, "error:testshl_1")}
            revert();
        }
        assembly {log1(0, 0, "success:testshl_1")}

        if (shl(4, 0xFF00000000000000000000000000000000000000000000000000000000000000) != 0xF000000000000000000000000000000000000000000000000000000000000000) {
            assembly {log1(0, 0, "error:testshl_FF")}
            revert();
        }
        assembly {log1(0, 0, "success:testshl_FF")}

        if (shr(1, 2) != 1) {
            assembly {log1(0, 0, "error:testshr_1")}
            revert();
        }
        assembly {log1(0, 0, "success:testshr_1")}

        if (shr(4, 0xFF) != 0xF) {
            assembly {log1(0, 0, "error:testshr_FF")}
            revert();
        }
        assembly {log1(0, 0, "success:testshr_FF")}

        if (sar(1, 2) != 1) {
            assembly {log1(0, 0, "error:testsar_1")}
            revert();
        }
        assembly {log1(0, 0, "success:testsar_1")}

        if (sar(4, 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF0) != 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF) {
            assembly {log1(0, 0, "error:testsar_FF")}
            revert();
        }
        assembly {log1(0, 0, "success:testsar_FF")}


        assembly {log1(0, 0, "success:")}
    }
}
