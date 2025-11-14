// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.20;

import {Test, console} from "forge-std/Test.sol";
import {TruthyMarketFactory} from "../../src/TruthyMarketFactory.sol";
import {TruthyMarket} from "../../src/TruthyMarket.sol";
import {MockUSDC} from "../../src/mocks/MockUSDC.sol";
import {Constants} from "../../src/libraries/Constants.sol";

/// @title TruthyMarketTest
/// @notice Comprehensive unit tests for TruthyMarket
contract TruthyMarketTest is Test {
    TruthyMarketFactory public factory;
    MockUSDC public usdc;
    TruthyMarket public market;

    address public owner = address(this);
    address public creator = address(0x1);
    address public resolver = address(0x2);
    address public alice = address(0x3);
    address public bob = address(0x4);

    bytes32 public marketId = keccak256("test-market-1");
    uint256 public expiresAt = block.timestamp + 30 days;
    uint256[2] public initialPrices = [0.5e18, 0.5e18];
    uint256 public initialLiquidity = 1000e6;

    function setUp() public {
        usdc = new MockUSDC();
        factory = new TruthyMarketFactory(address(usdc), 5e6, 200);

        // Setup addresses with USDC
        usdc.mint(creator, 100000e6);
        usdc.mint(alice, 10000e6);
        usdc.mint(bob, 10000e6);

        // Setup approvals
        vm.prank(creator);
        usdc.approve(address(factory), type(uint256).max);

        vm.prank(alice);
        usdc.approve(address(usdc), type(uint256).max);

        vm.prank(bob);
        usdc.approve(address(usdc), type(uint256).max);

        // Create market
        vm.prank(creator);
        market = factory.createMarket(
            marketId,
            "Will ETH reach $5000 by end of 2024?",
            "ETH price prediction market",
            "crypto",
            "https://twitter.com/test/123",
            resolver,
            expiresAt,
            initialPrices,
            initialLiquidity
        );

        // Approve market to spend users' USDC
        vm.prank(alice);
        usdc.approve(address(market), type(uint256).max);

        vm.prank(bob);
        usdc.approve(address(market), type(uint256).max);
    }

    // ============ Metadata Tests ============

    function test_MarketMetadata() public {
        assertEq(market.id(), marketId);
        assertEq(market.name(), "Will ETH reach $5000 by end of 2024?");
        assertEq(market.description(), "ETH price prediction market");
        assertEq(market.category(), "crypto");
        assertEq(market.sourceUrl(), "https://twitter.com/test/123");
        assertEq(market.creator(), creator);
        assertEq(market.getResolver(), resolver);
        assertEq(market.expiresAt(), expiresAt);
        assertFalse(market.isResolved());
    }

    function test_InitialPrices() public {
        uint256 yesPrice = market.getOutcomePrice(0);
        uint256 noPrice = market.getOutcomePrice(1);

        // Should be 50/50 initially
        assertEq(yesPrice, 0.5e18);
        assertEq(noPrice, 0.5e18);
    }

    function test_InitialLiquidity() public {
        uint256 totalLiquidity = market.getTotalLiquidity();
        assertEq(totalLiquidity, initialLiquidity);

        assertEq(market.getOutcomeLiquidity(0), initialLiquidity / 2);
        assertEq(market.getOutcomeLiquidity(1), initialLiquidity / 2);
    }

    // ============ Trading Tests ============

    function test_BuyYesOutcome() public {
        uint256 buyAmount = 100e18; // 100 outcome tokens
        uint256 aliceBalanceBefore = usdc.balanceOf(alice);

        vm.prank(alice);
        (uint256 cost, uint256 fee) = market.buyOutcome(0, buyAmount);

        // Verify Alice received tokens
        assertEq(market.getOutcomeToken(0).balanceOf(alice), buyAmount);

        // Verify payment
        assertEq(usdc.balanceOf(alice), aliceBalanceBefore - cost);

        // Verify fee collected
        assertGt(fee, 0);
        assertEq(market.accumulatedFees(), fee);

        // Verify volume tracked
        assertGt(market.totalVolume(), 0);
        assertGt(market.userVolume(alice), 0);
    }

    function test_BuyNoOutcome() public {
        uint256 buyAmount = 100e18;

        vm.prank(alice);
        (uint256 cost,) = market.buyOutcome(1, buyAmount);

        assertEq(market.getOutcomeToken(1).balanceOf(alice), buyAmount);
        assertGt(cost, 0);
    }

    function test_PriceChangesAfterBuy() public {
        uint256 yesPrice Before = market.getOutcomePrice(0);

        // Buy a large amount of YES
        vm.prank(alice);
        market.buyOutcome(0, 1000e18);

        uint256 yesPriceAfter = market.getOutcomePrice(0);

        // YES price should increase
        assertGt(yesPriceAfter, yesPrice Before);
    }

    function test_SellOutcome() public {
        // Alice buys first
        uint256 buyAmount = 100e18;
        vm.prank(alice);
        market.buyOutcome(0, buyAmount);

        uint256 aliceBalanceBefore = usdc.balanceOf(alice);
        uint256 outcomeBalanceBefore = market.getOutcomeToken(0).balanceOf(alice);

        // Alice sells half
        uint256 sellAmount = 50e18;
        vm.prank(alice);
        (uint256 proceeds, uint256 fee) = market.redeemOutcome(0, sellAmount);

        // Verify tokens burned
        assertEq(market.getOutcomeToken(0).balanceOf(alice), outcomeBalanceBefore - sellAmount);

        // Verify proceeds received
        assertEq(usdc.balanceOf(alice), aliceBalanceBefore + proceeds);
        assertGt(fee, 0);
    }

    function test_PreviewFunctions() public {
        uint256 buyAmount = 100e18;

        uint256 estimatedCost = market.previewCostToBuy(0, buyAmount);

        vm.prank(alice);
        (uint256 actualCost,) = market.buyOutcome(0, buyAmount);

        // Should be very close (may differ slightly due to fees)
        assertApproxEqRel(actualCost, estimatedCost, 0.02e18); // Within 2%
    }

    function testFail_BuyBelowMinimum() public {
        uint256 tooSmall = 0.1e6; // Below 0.5 USDC minimum

        vm.prank(alice);
        market.buyOutcome(0, tooSmall);
    }

    function testFail_BuyAboveMaximum() public {
        uint256 tooLarge = 2000e6; // Above 1000 USDC maximum
        usdc.mint(alice, 10000e6);

        vm.prank(alice);
        market.buyOutcome(0, tooLarge);
    }

    function testFail_SellMoreThanBalance() public {
        vm.prank(alice);
        market.buyOutcome(0, 100e18);

        vm.prank(alice);
        market.redeemOutcome(0, 200e18); // More than balance
    }

    function testFail_BuyAfterResolution() public {
        // Resolve market
        vm.warp(expiresAt + 1);
        vm.prank(resolver);
        market.resolve(0);

        // Try to buy
        vm.prank(alice);
        market.buyOutcome(0, 100e18);
    }

    // ============ Resolution Tests ============

    function test_Resolution() public {
        uint256 winningOutcome = 0; // YES wins

        // Fast forward to expiry
        vm.warp(expiresAt + 1);

        vm.prank(resolver);
        market.resolve(winningOutcome);

        assertTrue(market.isResolved());
    }

    function testFail_ResolveBeforeExpiry() public {
        vm.prank(resolver);
        market.resolve(0);
    }

    function testFail_ResolveByNonResolver() public {
        vm.warp(expiresAt + 1);

        vm.prank(alice);
        market.resolve(0);
    }

    function testFail_ResolveInvalidOutcome() public {
        vm.warp(expiresAt + 1);

        vm.prank(resolver);
        market.resolve(2); // Invalid index
    }

    function testFail_ResolveTwice() public {
        vm.warp(expiresAt + 1);

        vm.prank(resolver);
        market.resolve(0);

        vm.prank(resolver);
        market.resolve(0); // Try again
    }

    function test_WinningRedemption() public {
        uint256 buyAmount = 100e18;
        uint256 winningOutcome = 0; // YES wins

        // Alice buys YES
        vm.prank(alice);
        market.buyOutcome(0, buyAmount);

        // Resolve to YES
        vm.warp(expiresAt + 1);
        vm.prank(resolver);
        market.resolve(winningOutcome);

        // Alice redeems winning tokens
        uint256 aliceBalanceBefore = usdc.balanceOf(alice);

        vm.prank(alice);
        (uint256 proceeds, uint256 fee) = market.redeemOutcome(0, buyAmount);

        // Should get 1:1 redemption
        assertEq(proceeds, buyAmount);
        // No fee on winning redemption
        assertEq(fee, 0);
        // Balance should increase
        assertGt(usdc.balanceOf(alice), aliceBalanceBefore);
    }

    function test_LosingRedemption() public {
        uint256 buyAmount = 100e18;
        uint256 winningOutcome = 0; // YES wins

        // Bob buys NO
        vm.prank(bob);
        market.buyOutcome(1, buyAmount);

        // Resolve to YES
        vm.warp(expiresAt + 1);
        vm.prank(resolver);
        market.resolve(winningOutcome);

        // Bob redeems losing tokens
        uint256 bobBalanceBefore = usdc.balanceOf(bob);

        vm.prank(bob);
        (uint256 proceeds, uint256 fee) = market.redeemOutcome(1, buyAmount);

        // Should get nothing
        assertEq(proceeds, 0);
        assertEq(fee, 0);
        // Balance unchanged
        assertEq(usdc.balanceOf(bob), bobBalanceBefore);
    }

    // ============ Admin Tests ============

    function test_Pause() public {
        vm.prank(creator);
        market.pause();

        // Should not be able to buy
        vm.prank(alice);
        vm.expectRevert();
        market.buyOutcome(0, 100e18);
    }

    function test_Unpause() public {
        vm.prank(creator);
        market.pause();

        vm.prank(creator);
        market.unpause();

        // Should be able to buy again
        vm.prank(alice);
        market.buyOutcome(0, 100e18);
    }

    function test_SetBetLimits() public {
        uint256 newMin = 1e6; // $1
        uint256 newMax = 500e6; // $500

        vm.prank(creator);
        market.setBetLimits(newMin, newMax);

        assertEq(market.minBet(), newMin);
        assertEq(market.maxBet(), newMax);
    }

    function testFail_SetBetLimitsInvalid() public {
        vm.prank(creator);
        market.setBetLimits(100e6, 50e6); // Min > Max
    }

    function test_WithdrawFees() public {
        // Generate fees through trading
        vm.prank(alice);
        market.buyOutcome(0, 100e18);

        uint256 fees = market.accumulatedFees();
        assertGt(fees, 0);

        uint256 creatorBalanceBefore = usdc.balanceOf(creator);

        vm.prank(creator);
        market.withdrawFees(creator);

        assertEq(usdc.balanceOf(creator), creatorBalanceBefore + fees);
        assertEq(market.accumulatedFees(), 0);
    }

    // ============ Edge Cases ============

    function test_MultipleUsersTrading() public {
        // Alice buys YES
        vm.prank(alice);
        market.buyOutcome(0, 100e18);

        // Bob buys NO
        vm.prank(bob);
        market.buyOutcome(1, 100e18);

        // Verify both have tokens
        assertEq(market.getOutcomeToken(0).balanceOf(alice), 100e18);
        assertEq(market.getOutcomeToken(1).balanceOf(bob), 100e18);

        // Verify volume tracked separately
        assertGt(market.userVolume(alice), 0);
        assertGt(market.userVolume(bob), 0);
    }

    function test_LargeTradeImpact() public {
        uint256 smallBuy = 10e18;
        uint256 largeBuy = 1000e18;

        // Small buy
        vm.prank(alice);
        (uint256 smallCost,) = market.buyOutcome(0, smallBuy);

        // Get price change
        uint256 yesPrice = market.getOutcomePrice(0);

        // Large buy
        usdc.mint(bob, 100000e6);
        vm.prank(bob);
        usdc.approve(address(market), type(uint256).max);

        vm.prank(bob);
        (uint256 largeCost,) = market.buyOutcome(0, largeBuy);

        // Large buy should have proportionally higher cost
        assertGt(largeCost / largeBuy, smallCost / smallBuy);
    }

    function test_ZeroLiquidityMarket() public {
        // Create market with zero liquidity
        vm.prank(creator);
        TruthyMarket zeroLiqMarket = factory.createMarket(
            keccak256("zero-liq"),
            "Zero Liquidity Market",
            "Test",
            "crypto",
            "url",
            resolver,
            block.timestamp + 30 days,
            [0.5e18, 0.5e18],
            0
        );

        // Should still work, starting from 50/50
        assertEq(zeroLiqMarket.getTotalLiquidity(), 0);

        // But prices should still be defined
        uint256 yesPrice = zeroLiqMarket.getOutcomePrice(0);
        assertEq(yesPrice, 0.5e18); // Should default to 50%
    }

    // ============ Gas Benchmarks ============

    function testGas_BuyOutcome() public {
        vm.prank(alice);
        market.buyOutcome(0, 100e18);
    }

    function testGas_SellOutcome() public {
        vm.prank(alice);
        market.buyOutcome(0, 100e18);

        vm.prank(alice);
        market.redeemOutcome(0, 50e18);
    }

    function testGas_Resolve() public {
        vm.warp(expiresAt + 1);

        vm.prank(resolver);
        market.resolve(0);
    }
}
