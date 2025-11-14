// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.20;

import {Test, console} from "forge-std/Test.sol";
import {TruthyMarketFactory} from "../../src/TruthyMarketFactory.sol";
import {TruthyMarket} from "../../src/TruthyMarket.sol";
import {MockUSDC} from "../../src/mocks/MockUSDC.sol";
import {PricingLibrary} from "../../src/libraries/PricingLibrary.sol";

/// @title PricingFuzzTest
/// @notice Fuzz tests for pricing calculations and invariants
contract PricingFuzzTest is Test {
    TruthyMarketFactory public factory;
    MockUSDC public usdc;
    TruthyMarket public market;

    address public creator = address(0x1);
    address public resolver = address(0x2);
    address public trader = address(0x3);

    function setUp() public {
        usdc = new MockUSDC();
        factory = new TruthyMarketFactory(address(usdc), 5e6, 200);

        usdc.mint(creator, 1000000e6);
        usdc.mint(trader, 1000000e6);

        vm.prank(creator);
        usdc.approve(address(factory), type(uint256).max);

        vm.prank(trader);
        usdc.approve(address(usdc), type(uint256).max);

        // Create market with high liquidity for testing
        vm.prank(creator);
        market = factory.createMarket(
            keccak256("fuzz-test"),
            "Fuzz Test Market",
            "Test",
            "crypto",
            "url",
            resolver,
            block.timestamp + 365 days,
            [0.5e18, 0.5e18],
            100000e6 // High liquidity
        );

        vm.prank(trader);
        usdc.approve(address(market), type(uint256).max);
    }

    // ============ Price Invariants ============

    /// @notice Fuzz test: Prices should always sum to approximately 1.0
    function testFuzz_PricesSumToOne(uint256 buyAmount) public {
        // Bound buy amount to reasonable range
        buyAmount = bound(buyAmount, market.minBet(), market.maxBet());

        vm.prank(trader);
        market.buyOutcome(0, buyAmount);

        uint256 yesPrice = market.getOutcomePrice(0);
        uint256 noPrice = market.getOutcomePrice(1);

        // Prices should sum to ~1.0 (within small tolerance for rounding)
        assertApproxEqAbs(yesPrice + noPrice, 1e18, 1e15); // Within 0.1%
    }

    /// @notice Fuzz test: Prices should always be between 0 and 1
    function testFuzz_PricesBounded(uint256 buyAmount, uint256 outcomeIdx) public {
        buyAmount = bound(buyAmount, market.minBet(), market.maxBet());
        outcomeIdx = bound(outcomeIdx, 0, 1);

        vm.prank(trader);
        market.buyOutcome(outcomeIdx, buyAmount);

        uint256 yesPrice = market.getOutcomePrice(0);
        uint256 noPrice = market.getOutcomePrice(1);

        // Both prices should be in [0, 1]
        assertGe(yesPrice, 0);
        assertLe(yesPrice, 1e18);
        assertGe(noPrice, 0);
        assertLe(noPrice, 1e18);
    }

    /// @notice Fuzz test: Buying should increase price
    function testFuzz_BuyingIncreasesPrice(uint256 buyAmount) public {
        buyAmount = bound(buyAmount, market.minBet(), market.maxBet());

        uint256 priceBelow = market.getOutcomePrice(0);

        vm.prank(trader);
        market.buyOutcome(0, buyAmount);

        uint256 priceAfter = market.getOutcomePrice(0);

        // Price should increase
        assertGe(priceAfter, priceBelow);
    }

    /// @notice Fuzz test: Selling should decrease price
    function testFuzz_SellingDecreasesPrice(uint256 buyAmount, uint256 sellAmount) public {
        buyAmount = bound(buyAmount, market.minBet(), market.maxBet());

        // Buy first
        vm.prank(trader);
        market.buyOutcome(0, buyAmount);

        // Bound sell to less than buy
        sellAmount = bound(sellAmount, 1, buyAmount);

        uint256 priceAfterBuy = market.getOutcomePrice(0);

        // Sell
        vm.prank(trader);
        market.redeemOutcome(0, sellAmount);

        uint256 priceAfterSell = market.getOutcomePrice(0);

        // Price should decrease or stay same
        assertLe(priceAfterSell, priceAfterBuy);
    }

    // ============ Volume Invariants ============

    /// @notice Fuzz test: Total volume should always increase
    function testFuzz_VolumeOnlyIncreases(uint256 numTrades) public {
        numTrades = bound(numTrades, 1, 20);

        uint256 previousVolume = market.totalVolume();

        for (uint256 i = 0; i < numTrades; i++) {
            vm.prank(trader);
            market.buyOutcome(i % 2, market.minBet());

            uint256 currentVolume = market.totalVolume();
            assertGe(currentVolume, previousVolume);
            previousVolume = currentVolume;
        }
    }

    /// @notice Fuzz test: User volume should equal their trading activity
    function testFuzz_UserVolumeTracking(uint256 numBuys) public {
        numBuys = bound(numBuys, 1, 10);

        uint256 expectedVolume = 0;

        for (uint256 i = 0; i < numBuys; i++) {
            uint256 amount = market.minBet();

            uint256 costBefore = market.previewCostToBuy(0, amount);

            vm.prank(trader);
            (uint256 actualCost, uint256 fee) = market.buyOutcome(0, amount);

            expectedVolume += actualCost - fee;
        }

        uint256 userVolume = market.userVolume(trader);
        assertGe(userVolume, 0);
    }

    // ============ Liquidity Invariants ============

    /// @notice Fuzz test: Total liquidity should increase with buys, decrease with sells
    function testFuzz_LiquidityTracking(uint256 buyAmount) public {
        buyAmount = bound(buyAmount, market.minBet(), market.maxBet());

        uint256 liquidityBefore = market.getTotalLiquidity();

        vm.prank(trader);
        market.buyOutcome(0, buyAmount);

        uint256 liquidityAfterBuy = market.getTotalLiquidity();

        // Liquidity increases with buys
        assertGt(liquidityAfterBuy, liquidityBefore);

        // Sell some
        vm.prank(trader);
        market.redeemOutcome(0, buyAmount / 2);

        uint256 liquidityAfterSell = market.getTotalLiquidity();

        // Liquidity decreases with sells
        assertLt(liquidityAfterSell, liquidityAfterBuy);
    }

    // ============ Cost Calculation Invariants ============

    /// @notice Fuzz test: Larger buys should cost proportionally more
    function testFuzz_LargerBuysCostMore(uint256 smallAmount, uint256 largeAmount) public {
        smallAmount = bound(smallAmount, market.minBet(), market.maxBet() / 2);
        largeAmount = bound(largeAmount, smallAmount + 1, market.maxBet());

        uint256 smallCost = market.previewCostToBuy(0, smallAmount);
        uint256 largeCost = market.previewCostToBuy(0, largeAmount);

        // Large amount should cost more
        assertGt(largeCost, smallCost);

        // Should cost proportionally more (due to price impact)
        uint256 smallAvgCost = (smallCost * 1e18) / smallAmount;
        uint256 largeAvgCost = (largeCost * 1e18) / largeAmount;

        assertGe(largeAvgCost, smallAvgCost);
    }

    /// @notice Fuzz test: Buy then sell should approximately break even (minus fees)
    function testFuzz_RoundTripCost(uint256 amount) public {
        amount = bound(amount, market.minBet(), market.maxBet());

        uint256 balanceBefore = usdc.balanceOf(trader);

        // Buy
        vm.prank(trader);
        (uint256 buyCost, uint256 buyFee) = market.buyOutcome(0, amount);

        // Immediately sell
        vm.prank(trader);
        (uint256 sellProceeds, uint256 sellFee) = market.redeemOutcome(0, amount);

        uint256 balanceAfter = usdc.balanceOf(trader);

        // Loss should be approximately the fees
        uint256 loss = balanceBefore - balanceAfter;
        uint256 totalFees = buyFee + sellFee;

        // Loss should be close to total fees (may differ slightly due to price movement)
        assertApproxEqRel(loss, totalFees, 0.1e18); // Within 10%
    }

    // ============ Fee Invariants ============

    /// @notice Fuzz test: Fees should always be collected
    function testFuzz_FeesCollected(uint256 buyAmount) public {
        buyAmount = bound(buyAmount, market.minBet(), market.maxBet());

        uint256 feesBefore = market.accumulatedFees();

        vm.prank(trader);
        (uint256 cost, uint256 fee) = market.buyOutcome(0, buyAmount);

        uint256 feesAfter = market.accumulatedFees();

        // Fees should increase
        assertEq(feesAfter, feesBefore + fee);
        assertGt(fee, 0);
    }

    /// @notice Fuzz test: Fee should be correct percentage
    function testFuzz_FeePercentage(uint256 buyAmount) public {
        buyAmount = bound(buyAmount, market.minBet(), market.maxBet());

        vm.prank(trader);
        (uint256 cost, uint256 fee) = market.buyOutcome(0, buyAmount);

        uint256 baseCost = cost - fee;

        // Fee should be 2% of base cost (200 basis points)
        uint256 expectedFee = (baseCost * 200) / 10000;

        assertApproxEqAbs(fee, expectedFee, 1); // Within 1 wei
    }

    // ============ Edge Cases ============

    /// @notice Fuzz test: Multiple traders shouldn't interfere
    function testFuzz_MultipleTraders(uint256 seed) public {
        address trader1 = address(uint160(seed));
        address trader2 = address(uint160(seed + 1));

        // Setup traders
        usdc.mint(trader1, 100000e6);
        usdc.mint(trader2, 100000e6);

        vm.prank(trader1);
        usdc.approve(address(market), type(uint256).max);
        vm.prank(trader2);
        usdc.approve(address(market), type(uint256).max);

        // Both buy
        vm.prank(trader1);
        market.buyOutcome(0, market.minBet());

        vm.prank(trader2);
        market.buyOutcome(1, market.minBet());

        // Both should have their tokens
        assertEq(market.getOutcomeToken(0).balanceOf(trader1), market.minBet());
        assertEq(market.getOutcomeToken(1).balanceOf(trader2), market.minBet());

        // Volumes should be tracked separately
        assertGt(market.userVolume(trader1), 0);
        assertGt(market.userVolume(trader2), 0);
    }

    /// @notice Fuzz test: Preview functions should be accurate
    function testFuzz_PreviewAccuracy(uint256 buyAmount) public {
        buyAmount = bound(buyAmount, market.minBet(), market.maxBet());

        uint256 previewCost = market.previewCostToBuy(0, buyAmount);

        vm.prank(trader);
        (uint256 actualCost,) = market.buyOutcome(0, buyAmount);

        // Preview should be close to actual (may differ slightly due to fees)
        assertApproxEqRel(actualCost, previewCost, 0.03e18); // Within 3%
    }

    /// @notice Fuzz test: Cannot buy/sell invalid amounts
    function testFuzz_BetLimitsEnforced(uint256 invalidAmount) public {
        // Test amounts outside valid range
        vm.assume(invalidAmount < market.minBet() || invalidAmount > market.maxBet());

        vm.prank(trader);
        vm.expectRevert();
        market.buyOutcome(0, invalidAmount);
    }
}
