pragma solidity 0.8.7;

contract TestMath {
    function log(string memory message) private {
        assembly {
            // manually emit a technically invalid LOG1 that we 
            // can then recognize and parse in the testing routine
            log1(0x0, 0x0, message)
        }
    }

    function add(int a, int b) private pure returns (int) {
        return a + b;
    }

    function sub(int a, int b) private pure returns (int) {
        return a - b;
    }
  
    fallback() external {
        if (add(1, 2) != 3) {
            log("error:test_add");
            revert();
        }
        log("success:test_add");

        if (sub(2, 1) != 1) {
            log("error:test_sub");
            revert();
        }
        log("success:test_sub");

        log("success:");
    }
}
