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

    function test_1(string calldata _name) public{

        // this is the keccak of the "test_address" string
        uint256 test_address = 0xcf0b1b5014de87f401af85ff4516711708f22a5140af0526c338de218bd6b126;

        uint deadbeef = 0xdeadbeef;
        bytes32 deadbeef_b = bytes32(abi.encodePacked(deadbeef));

        assembly{
            sstore(test_address, deadbeef_b)
        }

        uint256 sha_res = uint256(keccak256(abi.encodePacked(_name)));

        if(sha_res != test_address){
            assembly {log1(0, 0, "error:test_lamb_sha_concrete1")}
        } else {
            assembly {log1(0, 0, "success:test_lamb_sha_concrete1")}
        }           
    }
}