// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.20;

import {Math} from "@openzeppelin/contracts/utils/math/Math.sol";

/// @title PricingLibrary
/// @notice Reusable pricing calculations for prediction markets
/// @dev Uses simple supply-based pricing: price = supply[i] / totalSupply
library PricingLibrary {
    using Math for uint256;

    uint256 private constant PRECISION = 1e18;

    /// @notice Calculate the current price of an outcome
    /// @param outcomeSupply Supply of the specific outcome
    /// @param totalSupply Total supply of all outcomes
    /// @return price Price as a fraction of PRECISION (1e18 = 100%)
    function calculatePrice(uint256 outcomeSupply, uint256 totalSupply) internal pure returns (uint256 price) {
        if (totalSupply == 0) return PRECISION / 2; // Default to 50%
        return outcomeSupply.mulDiv(PRECISION, totalSupply);
    }

    /// @notice Calculate price after minting new outcome tokens
    /// @param outcomeSupply Current outcome supply
    /// @param totalSupply Current total supply
    /// @param amount Amount to mint
    /// @return price New price after minting
    function calculatePriceAfterMint(uint256 outcomeSupply, uint256 totalSupply, uint256 amount)
        internal
        pure
        returns (uint256 price)
    {
        return (outcomeSupply + amount).mulDiv(PRECISION, totalSupply + amount);
    }

    /// @notice Calculate price after burning outcome tokens
    /// @param outcomeSupply Current outcome supply
    /// @param totalSupply Current total supply
    /// @param amount Amount to burn
    /// @return price New price after burning
    function calculatePriceAfterBurn(uint256 outcomeSupply, uint256 totalSupply, uint256 amount)
        internal
        pure
        returns (uint256 price)
    {
        return (outcomeSupply - amount).mulDiv(PRECISION, totalSupply - amount);
    }

    /// @notice Calculate average price for minting (prevents front-running)
    /// @param currentPrice Current price before mint
    /// @param priceAfterMint Price after mint
    /// @return averagePrice Average of current and post-mint price
    function calculateAveragePriceForMint(uint256 currentPrice, uint256 priceAfterMint)
        internal
        pure
        returns (uint256 averagePrice)
    {
        return Math.average(currentPrice, priceAfterMint);
    }

    /// @notice Calculate average price for burning
    /// @param currentPrice Current price before burn
    /// @param priceAfterBurn Price after burn
    /// @return averagePrice Average of current and post-burn price
    function calculateAveragePriceForBurn(uint256 currentPrice, uint256 priceAfterBurn)
        internal
        pure
        returns (uint256 averagePrice)
    {
        return Math.average(currentPrice, priceAfterBurn);
    }

    /// @notice Calculate cost to mint outcome tokens
    /// @param outcomeSupply Current outcome supply
    /// @param totalSupply Current total supply
    /// @param amount Amount to mint
    /// @return cost Cost in base currency units
    function calculateMintCost(uint256 outcomeSupply, uint256 totalSupply, uint256 amount)
        internal
        pure
        returns (uint256 cost)
    {
        uint256 currentPrice = calculatePrice(outcomeSupply, totalSupply);
        uint256 priceAfterMint = calculatePriceAfterMint(outcomeSupply, totalSupply, amount);
        uint256 averagePrice = calculateAveragePriceForMint(currentPrice, priceAfterMint);

        return amount.mulDiv(averagePrice, PRECISION);
    }

    /// @notice Calculate proceeds from burning outcome tokens
    /// @param outcomeSupply Current outcome supply
    /// @param totalSupply Current total supply
    /// @param amount Amount to burn
    /// @return proceeds Proceeds in base currency units
    function calculateBurnProceeds(uint256 outcomeSupply, uint256 totalSupply, uint256 amount)
        internal
        pure
        returns (uint256 proceeds)
    {
        uint256 currentPrice = calculatePrice(outcomeSupply, totalSupply);
        uint256 priceAfterBurn = calculatePriceAfterBurn(outcomeSupply, totalSupply, amount);
        uint256 averagePrice = calculateAveragePriceForBurn(currentPrice, priceAfterBurn);

        return amount.mulDiv(averagePrice, PRECISION);
    }
}
