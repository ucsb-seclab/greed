// SPDX-License-Identifier: GPL-3.0

pragma solidity 0.8.7;

contract TestShaRewrite {

    fallback() external {
        uint a;
        uint b;

        assembly {
            mstore(1000, 42)
            mstore(2000, 42)
            a := keccak256(1000, 32)
            b := keccak256(2000, 32)
        }

        if (a != b) {
            revert();
        } else {
        }


        assembly {
            mstore(1000, 43)
            a := keccak256(1000, 32)
        }

        if (a == b) {
            assembly {log1(0, 0, "error:test_sha_rewrite")}
            revert();
        } else {
            assembly {log1(0, 0, "success:test_sha_rewrite")}
        }

        assembly {log1(0, 0, "success:")}
    }

}
