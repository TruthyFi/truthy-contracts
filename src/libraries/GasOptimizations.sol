// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.20;

/// @title GasOptimizations
/// @notice Gas optimization utilities and patterns
/// @dev Use these patterns throughout contracts for gas efficiency
library GasOptimizations {
    /// @notice Optimized loop for array operations
    /// @dev Uses unchecked increment for gas savings
    /// @param length Array length
    /// @return i Current index (for use in loop)
    function optimizedLoop(uint256 length) internal pure returns (uint256 i) {
        assembly {
            i := 0
        }
    }

    /// @notice Increment loop counter (unchecked for gas savings)
    /// @dev Only use when overflow is impossible
    /// @param i Current index
    /// @return Next index
    function incrementUnchecked(uint256 i) internal pure returns (uint256) {
        unchecked {
            return i + 1;
        }
    }

    /// @notice Pack two uint128 values into one uint256 slot
    /// @param a First value (max uint128)
    /// @param b Second value (max uint128)
    /// @return packed Packed value
    function packUint128(uint128 a, uint128 b) internal pure returns (uint256 packed) {
        assembly {
            packed := or(shl(128, a), b)
        }
    }

    /// @notice Unpack uint256 into two uint128 values
    /// @param packed Packed value
    /// @return a First value
    /// @return b Second value
    function unpackUint128(uint256 packed) internal pure returns (uint128 a, uint128 b) {
        assembly {
            a := shr(128, packed)
            b := and(packed, 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF)
        }
    }

    /// @notice Efficient boolean to uint conversion
    /// @param b Boolean value
    /// @return u Uint value (0 or 1)
    function boolToUint(bool b) internal pure returns (uint256 u) {
        assembly {
            u := b
        }
    }

    /// @notice Check if address is zero (gas optimized)
    /// @param addr Address to check
    /// @return isZero True if address is zero
    function isZeroAddress(address addr) internal pure returns (bool isZero) {
        assembly {
            isZero := iszero(addr)
        }
    }
}
