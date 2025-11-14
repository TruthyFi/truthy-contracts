// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.20;

/// @title Constants
/// @notice Centralized constant values for the TruthyFi protocol
library Constants {
    /// @notice Precision for price calculations (1e18 = 100%)
    uint256 internal constant PRECISION = 1e18;

    /// @notice Fee precision in basis points (10000 = 100%)
    uint256 internal constant FEE_PRECISION = 10000;

    /// @notice Maximum protocol fee rate (10%)
    uint256 internal constant MAX_FEE_RATE = 1000; // 10% in basis points

    /// @notice Number of binary outcomes (YES/NO)
    uint256 internal constant NUM_OUTCOMES = 2;

    /// @notice Index for YES outcome
    uint256 internal constant YES_INDEX = 0;

    /// @notice Index for NO outcome
    uint256 internal constant NO_INDEX = 1;

    /// @notice Default minimum bet (0.5 USDC with 6 decimals)
    uint256 internal constant DEFAULT_MIN_BET = 0.5e6;

    /// @notice Default maximum bet (1000 USDC with 6 decimals)
    uint256 internal constant DEFAULT_MAX_BET = 1000e6;

    /// @notice Default creation fee (5 USDC with 6 decimals)
    uint256 internal constant DEFAULT_CREATION_FEE = 5e6;

    /// @notice Default protocol fee rate (2%)
    uint256 internal constant DEFAULT_PROTOCOL_FEE_RATE = 200; // 2% in basis points
}
