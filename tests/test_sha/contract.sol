// SPDX-License-Identifier: GPL-3.0

pragma solidity 0.8.7;

contract TestSha {

    fallback() external {
        uint a;
        uint b;

        assembly {
            mstore(1024, 42)
            mstore(2048, 42)
            a := keccak256(1024, 32)
            b := keccak256(2048, 32)
        }

        if (a != b) {
            assembly {log1(0, 0, "error:test_sha_equal")}
            revert();
        } else {
            assembly {log1(0, 0, "success:test_sha_equal")}
        }

        assembly {
            mstore(1024, 42)
            mstore(2048, 43)
            a := keccak256(1024, 32)
            b := keccak256(2048, 32)
        }

        if (a == b) {
            assembly {log1(0, 0, "error:test_sha_different")}
            revert();
        } else {
            assembly {log1(0, 0, "success:test_sha_different")}
        }


    }

}
