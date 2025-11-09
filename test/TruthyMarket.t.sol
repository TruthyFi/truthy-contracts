// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.20;

import {Test, console} from "forge-std/Test.sol";
import {TruthyMarketFactory} from "../src/TruthyMarketFactory.sol";
import {TruthyMarket} from "../src/TruthyMarket.sol";
import {MockUSDC} from "../src/mocks/MockUSDC.sol";

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
    string public marketName = "Will ETH reach $5000 by end of 2024?";
    string public marketDescription = "ETH price prediction market";
    string public category = "crypto";
    string public sourceUrl = "https://twitter.com/test/123";
    uint256 public expiresAt = block.timestamp + 30 days;
    uint256[2] public initialPrices = [0.5e18, 0.5e18]; // 50/50
    uint256 public initialLiquidity = 1000e6; // 1000 USDC

    uint256 public constant CREATION_FEE = 5e6; // 5 USDC
    uint256 public constant PROTOCOL_FEE_RATE = 200; // 2%

    function setUp() public {
        // Deploy mock USDC
        usdc = new MockUSDC();

        // Deploy factory
        factory = new TruthyMarketFactory(address(usdc), CREATION_FEE, PROTOCOL_FEE_RATE);

        // Mint USDC to test addresses
        usdc.mint(creator, 10000e6);
        usdc.mint(alice, 10000e6);
        usdc.mint(bob, 10000e6);

        // Creator approves factory to spend USDC
        vm.startPrank(creator);
        usdc.approve(address(factory), type(uint256).max);
        vm.stopPrank();

        // Create a test market
        vm.startPrank(creator);
        market = factory.createMarket(
            marketId,
            marketName,
            marketDescription,
            category,
            sourceUrl,
            resolver,
            expiresAt,
            initialPrices,
            initialLiquidity
        );
        vm.stopPrank();

        // Setup approvals for Alice and Bob
        vm.prank(alice);
        usdc.approve(address(market), type(uint256).max);

        vm.prank(bob);
        usdc.approve(address(market), type(uint256).max);
    }

    function testFactoryDeployment() public {
        assertEq(address(factory.paymentToken()), address(usdc));
        assertEq(factory.creationFee(), CREATION_FEE);
        assertEq(factory.protocolFeeRate(), PROTOCOL_FEE_RATE);
    }

    function testMarketCreation() public {
        assertTrue(factory.marketExists(marketId));
        assertEq(address(factory.getMarket(marketId)), address(market));
        assertEq(factory.getTotalMarkets(), 1);
    }

    function testMarketMetadata() public {
        assertEq(market.id(), marketId);
        assertEq(market.name(), marketName);
        assertEq(market.description(), marketDescription);
        assertEq(market.category(), category);
        assertEq(market.sourceUrl(), sourceUrl);
        assertEq(market.creator(), creator);
        assertEq(market.getResolver(), resolver);
        assertEq(market.expiresAt(), expiresAt);
        assertFalse(market.isResolved());
    }

    function testBuyOutcome() public {
        uint256 buyAmount = 100e18; // 100 outcome tokens
        uint256 outcomeIdx = 0; // YES

        uint256 aliceBalanceBefore = usdc.balanceOf(alice);

        vm.prank(alice);
        (uint256 cost, uint256 fee) = market.buyOutcome(outcomeIdx, buyAmount);

        // Check Alice received outcome tokens
        assertEq(market.getOutcomeToken(outcomeIdx).balanceOf(alice), buyAmount);

        // Check Alice paid the cost
        assertEq(usdc.balanceOf(alice), aliceBalanceBefore - cost);

        // Check fee was collected
        assertGt(fee, 0);
        assertEq(market.accumulatedFees(), fee);

        // Check volume tracking
        assertEq(market.totalVolume(), cost - fee);
        assertEq(market.userVolume(alice), cost - fee);
    }

    function testSellOutcome() public {
        uint256 buyAmount = 100e18;
        uint256 outcomeIdx = 0;

        // Alice buys first
        vm.prank(alice);
        market.buyOutcome(outcomeIdx, buyAmount);

        uint256 aliceBalanceBefore = usdc.balanceOf(alice);
        uint256 outcomeBalanceBefore = market.getOutcomeToken(outcomeIdx).balanceOf(alice);

        // Alice sells half
        uint256 sellAmount = 50e18;
        vm.prank(alice);
        (uint256 proceeds, uint256 fee) = market.redeemOutcome(outcomeIdx, sellAmount);

        // Check Alice's outcome tokens decreased
        assertEq(market.getOutcomeToken(outcomeIdx).balanceOf(alice), outcomeBalanceBefore - sellAmount);

        // Check Alice received proceeds
        assertEq(usdc.balanceOf(alice), aliceBalanceBefore + proceeds);

        // Check fee was collected
        assertGt(fee, 0);
    }

    function testResolution() public {
        uint256 winningOutcome = 0; // YES wins

        // Fast forward to expiry
        vm.warp(expiresAt + 1);

        // Resolver resolves the market
        vm.prank(resolver);
        market.resolve(winningOutcome);

        assertTrue(market.isResolved());
    }

    function testRedemptionAfterResolution() public {
        uint256 buyAmount = 100e18;
        uint256 winningOutcome = 0; // YES

        // Alice buys YES tokens
        vm.prank(alice);
        market.buyOutcome(0, buyAmount);

        // Bob buys NO tokens
        vm.prank(bob);
        market.buyOutcome(1, buyAmount);

        // Resolve to YES
        vm.warp(expiresAt + 1);
        vm.prank(resolver);
        market.resolve(winningOutcome);

        // Alice redeems winning tokens (1:1, no fee)
        uint256 aliceBalanceBefore = usdc.balanceOf(alice);
        vm.prank(alice);
        (uint256 aliceProceeds, uint256 aliceFee) = market.redeemOutcome(0, buyAmount);

        assertEq(aliceProceeds, buyAmount); // 1:1 redemption
        assertEq(aliceFee, 0); // No fee on winning redemption
        assertGt(usdc.balanceOf(alice), aliceBalanceBefore);

        // Bob redeems losing tokens (gets nothing)
        uint256 bobBalanceBefore = usdc.balanceOf(bob);
        vm.prank(bob);
        (uint256 bobProceeds, uint256 bobFee) = market.redeemOutcome(1, buyAmount);

        assertEq(bobProceeds, 0); // Losing tokens are worthless
        assertEq(bobFee, 0);
        assertEq(usdc.balanceOf(bob), bobBalanceBefore); // No change
    }

    function testCannotBuyBelowMinimum() public {
        uint256 tooSmall = 0.1e6; // Less than 0.5 USDC minimum

        vm.prank(alice);
        vm.expectRevert("Below min bet");
        market.buyOutcome(0, tooSmall);
    }

    function testCannotBuyAboveMaximum() public {
        uint256 tooLarge = 2000e6; // More than 1000 USDC maximum

        // Mint more USDC to Alice
        usdc.mint(alice, 10000e6);

        vm.prank(alice);
        vm.expectRevert("Above max bet");
        market.buyOutcome(0, tooLarge);
    }

    function testCannotResolveBeforeExpiry() public {
        vm.prank(resolver);
        vm.expectRevert("Market not expired");
        market.resolve(0);
    }

    function testCannotResolveByNonResolver() public {
        vm.warp(expiresAt + 1);

        vm.prank(alice);
        vm.expectRevert("Only resolver");
        market.resolve(0);
    }

    function testPauseAndUnpause() public {
        // Owner can pause
        vm.prank(creator);
        market.pause();

        // Cannot buy when paused
        vm.prank(alice);
        vm.expectRevert();
        market.buyOutcome(0, 100e18);

        // Owner can unpause
        vm.prank(creator);
        market.unpause();

        // Can buy again
        vm.prank(alice);
        market.buyOutcome(0, 100e18);
    }

    function testWithdrawFees() public {
        // Generate some fees
        vm.prank(alice);
        market.buyOutcome(0, 100e18);

        uint256 fees = market.accumulatedFees();
        assertGt(fees, 0);

        uint256 ownerBalanceBefore = usdc.balanceOf(creator);

        // Owner withdraws fees
        vm.prank(creator);
        market.withdrawFees(creator);

        assertEq(usdc.balanceOf(creator), ownerBalanceBefore + fees);
        assertEq(market.accumulatedFees(), 0);
    }

    function testBetLimitsUpdate() public {
        uint256 newMin = 1e6; // $1
        uint256 newMax = 500e6; // $500

        vm.prank(creator);
        market.setBetLimits(newMin, newMax);

        assertEq(market.minBet(), newMin);
        assertEq(market.maxBet(), newMax);
    }

    function testMarketsByCreator() public {
        bytes32[] memory markets = factory.getMarketsByCreator(creator);
        assertEq(markets.length, 1);
        assertEq(markets[0], marketId);
    }

    function testMarketsByCategory() public {
        bytes32[] memory markets = factory.getMarketsByCategory(category);
        assertEq(markets.length, 1);
        assertEq(markets[0], marketId);
    }
}
