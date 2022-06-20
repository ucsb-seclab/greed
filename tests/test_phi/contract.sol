pragma solidity 0.8.7;

contract TestPhi {
    uint symbol;

    fallback() external payable {

        uint branch = 0;

        if (symbol == 1) {
            branch = 1;
        }

        if ((branch == 1) && (symbol != 1)) {
            assembly {log1(0, 0, "error:test_phi_impossible_branch")}
            revert();
        }

        assembly {log1(0, 0, "success:")}
    }
}
