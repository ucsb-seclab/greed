pragma solidity ^0.8.0;

contract TestSafeMath {
    uint256 public result;
    int256 public s_result;

    function add(uint256 a, uint256 b) private pure returns (uint256) {
        return (a + b);
    }

    function add_signed(int256 a, int256 b) private pure returns (int256) {
        return a + b;
    }

    function sub(uint256 a, uint256 b) private pure returns (uint256) {
        return a - b;
    }

    function sub_signed(int256 a, int256 b) private pure returns (int256) {
        return a - b;
    }

    function mul(uint256 a, uint256 b) private pure returns (uint256) {
        return a * b;
    }

    function mul_signed(int256 a, int256 b) private pure returns (int256) {
        return a * b;
    }

    function _testDiv1(uint256 a, uint256 b) public {
        // unused, necessary to avoid inlining of 'div'
        result = (20 * a) / b;
    }

    function div(uint256 a, uint256 b) private pure returns (uint256) {
        return a / b;
    }

    function _testSdiv1(int256 a, int256 b) public {
        s_result = (20 * a) / b;
    }

    function sdiv(int256 a, int256 b) private pure returns (int256) {
        return a / b;
    }

    function _testMod1(uint256 a, uint256 b) public {
        result = (20 * a) % b;
    }

    function mod(uint256 a, uint256 b) private pure returns (uint256) {
        return a % b;
    }

    function _testSMod1(int256 a, int256 b) public {
        s_result = (20 * a) % b;
    }

    function smod(int256 a, int256 b) private pure returns (int256) {
        return a % b;
    }

    fallback() external {

        if (add(10, 10) != 20) {
            assembly {log1(0, 0, "error:test_add")}
            revert();
        }
        assembly {log1(0, 0, "success:test_add")}

        if (add_signed(-10, -10) != -20) {
            assembly {log1(0, 0, "error:test_add_signed")}
            revert();
        }
        assembly {log1(0, 0, "success:test_add_signed")}

        if (sub(10, 10) != 0) {
            assembly {log1(0, 0, "error:test_sub")}
            revert();
        }
        assembly {log1(0, 0, "success:test_sub")}

        if (sub_signed(-10, -10) != 0) {
            assembly {log1(0, 0, "error:test_sub_signed")}
            revert();
        }
        assembly {log1(0, 0, "success:test_sub_signed")}

        if (mul(10, 10) != 100) {
            assembly {log1(0, 0, "error:test_mul")}
            revert();
        }
        assembly {log1(0, 0, "success:test_mul")}

        if (mul_signed(-10, -10) != 100) {
            assembly {log1(0, 0, "error:test_mul_signed")}
            revert();
        }
        assembly {log1(0, 0, "success:test_mul_signed")}

        if (div(10, 5) != 2) {
            assembly {log1(0, 0, "error:test_div")}
            revert();
        }
        assembly {log1(0, 0, "success:test_div")}

        if (sdiv(-10, -5) != 2) {
            assembly {log1(0, 0, "error:test_div_signed")}
            revert();
        }
        assembly {log1(0, 0, "success:test_div_signed")}

        if (div(1, 2) != 0) {
            assembly {log1(0, 0, "error:test_div_lt")}
            revert();
        }
        assembly {log1(0, 0, "success:test_div_lt")}

        if (sdiv(-1, 2) != 0) {
            assembly {log1(0, 0, "error:test_div_signed_lt")}
            revert();
        }
        assembly {log1(0, 0, "success:test_div_signed_lt")}

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

        if (smod(17, 5) != 2) {
            assembly {log1(0, 0, "error:test_smod_5")}
            revert();
        }
        assembly {log1(0, 0, "success:test_smod_5")}

        if (smod(-10, 3) != -1) {
            assembly {log1(0, 0, "error:test_smod_neg_3")}
            revert();
        }
        assembly {log1(0, 0, "success:test_smod_neg_3")}

        assembly {log1(0, 0, "success:")}
    }


}
