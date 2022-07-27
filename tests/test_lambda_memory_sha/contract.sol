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
        
        bool can_be_equal = false;

        // this is the keccak of the "test_address" string
        uint256 test_address = 0xcf0b1b5014de87f401af85ff4516711708f22a5140af0526c338de218bd6b126;

        uint deadbeef = 0xdeadbeef;
        bytes32 deadbeef_b = bytes32(abi.encodePacked(deadbeef));
        
        assembly{
            sstore(test_address, deadbeef_b)
        }

        uint256 sha_res = uint256(keccak256(abi.encodePacked(_name)));

        bytes32 mem_data = sload(sha_res);

        // We can only check if this is possible, NOT that this MUST happen.
        if(mem_data == deadbeef_b){
            can_be_equal = true;
        }

        if(can_be_equal == true){
            assembly {log1(0, 0, "success:test_lamb_sha_mem")}
            assembly {log1(0, 0, "success:")}
           
        }            
    }
}