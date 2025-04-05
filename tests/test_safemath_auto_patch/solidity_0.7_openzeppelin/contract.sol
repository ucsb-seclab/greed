pragma solidity ^0.7.0;

import "safemath.sol";

contract TestSafeMath {
    using SafeMath for uint256;

    uint256 public result;
    int256 public s_result;

    function add(uint256 a, uint256 b) private pure returns (uint256) {
        return a.add(b);
    }

    function sub(uint256 a, uint256 b) private pure returns (uint256) {
        return a.sub(b);
    }

    function _dumbMul(uint256 a, uint256 b) public {
        result = (a * 20).mul(b);
    }

    function mul(uint256 a, uint256 b) private pure returns (uint256) {
        return a.mul(b);
    }

    function div(uint256 a, uint256 b) private pure returns (uint256) {
        return a.div(b);
    }

    function mod(uint256 a, uint256 b) private pure returns (uint256) {
        return a.mod(b);
    }

    fallback() external {

        if (add(10, 10) != 20) {
            assembly {log1(0, 0, "error:test_add")}
            revert();
        }
        assembly {log1(0, 0, "success:test_add")}

        if (sub(10, 10) != 0) {
            assembly {log1(0, 0, "error:test_sub")}
            revert();
        }
        assembly {log1(0, 0, "success:test_sub")}

        if (mul(10, 10) != 100) {
            assembly {log1(0, 0, "error:test_mul")}
            revert();
        }
        assembly {log1(0, 0, "success:test_mul")}

        if (div(10, 5) != 2) {
            assembly {log1(0, 0, "error:test_div")}
            revert();
        }
        assembly {log1(0, 0, "success:test_div")}

        if (div(1, 2) != 0) {
            assembly {log1(0, 0, "error:test_div_lt")}
            revert();
        }
        assembly {log1(0, 0, "success:test_div_lt")}

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

        assembly {log1(0, 0, "success:")}
    }


}
