// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.20;

import {ERC20} from "@openzeppelin/contracts/token/ERC20/ERC20.sol";

/// @notice Mock USDC token for testing (6 decimals like real USDC)
contract MockUSDC is ERC20 {
    constructor() ERC20("Mock USDC", "USDC") {}

    function decimals() public pure override returns (uint8) {
        return 6; // USDC has 6 decimals
    }

    /// @notice Mint tokens for testing (anyone can mint in testnet)
    function mint(address to, uint256 amount) external {
        _mint(to, amount);
    }

    /// @notice Faucet function - get 1000 USDC for testing
    function faucet() external {
        _mint(msg.sender, 1000 * 10 ** decimals());
    }
}
