// SPDX-License-Identifier: GPL-3.0

pragma solidity 0.8.7;

contract TestSha {

    fallback() external {
        uint a;
        uint b;
        uint c;
        uint d;

        uint index1 = 1024*1;
        uint index2 = 1024*2;

        assembly {
            mstore(index1, 0x0000000000000000000000000000000000000000000000000000000000000000ffffffff00000000)
            mstore(index2, 0x0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffff)
            a := keccak256(index1, 32)
            b := keccak256(index2, 32)
        }

        if (a == b) {
            assembly {log1(0, 0, "error:test_sha_diff0xff")}
            revert();
        } else {
            assembly {log1(0, 0, "success:test_sha_diff0xff")}
        }


        assembly {
            c := keccak256(index1, 28)
            d := keccak256(index2, 28)
        }

        if (c != d) {
            assembly {log1(0, 0, "error:test_sha_diff0xffpartial")}
            revert();
        } else {
            assembly {log1(0, 0, "success:test_sha_diff0xffpartial")}
        }

        assembly {log1(0, 0, "success:")}
    }

}
