// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.20;

/// @title Errors
/// @notice Custom error definitions for gas-efficient error handling
library Errors {
    // Factory Errors
    error InvalidPaymentToken();
    error FeeRateTooHigh();
    error MarketAlreadyExists();
    error ExpiryMustBeInFuture();
    error EmptyMarketName();
    error InvalidResolver();
    error InvalidAddress();
    error NoFeesToWithdraw();

    // Market Errors
    error InvalidIndex();
    error BelowMinBet();
    error AboveMaxBet();
    error MarketResolved();
    error MarketNotExpired();
    error OnlyResolver();
    error InsufficientBalance();
    error InvalidPriceSum();
    error InvalidPrice();
    error ExpiryInPast();
    error MinBetGreaterThanMax();
    error MinBetMustBePositive();
    error MarketNotResolved();
    error AlreadyResolved();
}
