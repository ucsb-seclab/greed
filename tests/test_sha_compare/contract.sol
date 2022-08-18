pragma solidity 0.8.7;

contract TestMemory {

    function mload(uint offset) private pure returns (bytes32 value) {
        assembly {
            value := mload(offset)
        }
    }

    function sload(uint offset) private view returns (bytes32 value) {
        assembly {
            value := sload(offset)
        }
    }

    function test_1() public{
        
        uint256 sha_res = uint256(keccak256(abi.encodePacked("fabio_rulez")));

        if(sha_res == 0xcf0b1b5014de87f401af85ff4516711708f22a5140af0526c338de218bd6b126){
            assembly {log1(0, 0, "error:test_sha_compare_eq")}
        } else {
            assembly {log1(0, 0, "success:test_sha_compare_diff")}
        }           
    }
}