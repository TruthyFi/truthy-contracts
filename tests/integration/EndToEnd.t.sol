// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.20;

import {Test, console} from "forge-std/Test.sol";
import {TruthyMarketFactory} from "../../src/TruthyMarketFactory.sol";
import {TruthyMarket} from "../../src/TruthyMarket.sol";
import {MockUSDC} from "../../src/mocks/MockUSDC.sol";

/// @title EndToEndTest
/// @notice Integration tests for complete user journeys
contract EndToEndTest is Test {
    TruthyMarketFactory public factory;
    MockUSDC public usdc;

    address public factoryOwner = address(this);
    address public marketCreator = address(0x1);
    address public resolver = address(0x2);
    address public trader1 = address(0x3);
    address public trader2 = address(0x4);
    address public trader3 = address(0x5);

    function setUp() public {
        usdc = new MockUSDC();
        factory = new TruthyMarketFactory(address(usdc), 5e6, 200);

        // Fund all participants
        address[] memory users = new address[](4);
        users[0] = marketCreator;
        users[1] = trader1;
        users[2] = trader2;
        users[3] = trader3;

        for (uint256 i = 0; i < users.length; i++) {
            usdc.mint(users[i], 10000e6);
            vm.prank(users[i]);
            usdc.approve(address(factory), type(uint256).max);
        }
    }

    /// @notice Test complete lifecycle: create → trade → resolve → claim
    function test_CompleteMarketLifecycle() public {
        // 1. Market Creator creates a market
        bytes32 marketId = keccak256("eth-5000-2024");

        vm.prank(marketCreator);
        TruthyMarket market = factory.createMarket(
            marketId,
            "Will ETH reach $5000 by end of 2024?",
            "ETH price prediction",
            "crypto",
            "https://twitter.com/prediction",
            resolver,
            block.timestamp + 60 days,
            [0.3e18, 0.7e18], // 30% YES, 70% NO initially
            2000e6 // $2000 initial liquidity
        );

        vm.prank(trader1);
        usdc.approve(address(market), type(uint256).max);
        vm.prank(trader2);
        usdc.approve(address(market), type(uint256).max);
        vm.prank(trader3);
        usdc.approve(address(market), type(uint256).max);

        // Verify market created
        assertTrue(factory.marketExists(marketId));
        assertEq(market.creator(), marketCreator);

        // 2. Traders buy positions
        uint256 trader1InitialBalance = usdc.balanceOf(trader1);
        uint256 trader2InitialBalance = usdc.balanceOf(trader2);

        // Trader1 is bullish (buys YES)
        vm.prank(trader1);
        (uint256 cost1,) = market.buyOutcome(0, 500e18);

        // Trader2 is bearish (buys NO)
        vm.prank(trader2);
        (uint256 cost2,) = market.buyOutcome(1, 300e18);

        // Trader3 also buys YES
        vm.prank(trader3);
        market.buyOutcome(0, 200e18);

        // Verify positions
        assertEq(market.getOutcomeToken(0).balanceOf(trader1), 500e18);
        assertEq(market.getOutcomeToken(1).balanceOf(trader2), 300e18);
        assertEq(market.getOutcomeToken(0).balanceOf(trader3), 200e18);

        // Verify payments
        assertEq(usdc.balanceOf(trader1), trader1InitialBalance - cost1);
        assertEq(usdc.balanceOf(trader2), trader2InitialBalance - cost2);

        // 3. Some traders change positions (sell)
        uint256 trader1BalanceBeforeSell = usdc.balanceOf(trader1);

        vm.prank(trader1);
        (uint256 proceeds,) = market.redeemOutcome(0, 100e18);

        // Verify trader1 got proceeds
        assertEq(usdc.balanceOf(trader1), trader1BalanceBeforeSell + proceeds);
        assertEq(market.getOutcomeToken(0).balanceOf(trader1), 400e18);

        // 4. Market expires and resolver resolves
        vm.warp(block.timestamp + 60 days + 1);

        uint256 winningOutcome = 0; // YES wins
        vm.prank(resolver);
        market.resolve(winningOutcome);

        assertTrue(market.isResolved());

        // 5. Winners claim their rewards
        uint256 trader1FinalBalance = usdc.balanceOf(trader1);

        vm.prank(trader1);
        (uint256 winnings1,) = market.redeemOutcome(0, 400e18);

        // Trader1 should get 1:1 redemption
        assertEq(winnings1, 400e18);
        assertEq(usdc.balanceOf(trader1), trader1FinalBalance + winnings1);

        // Trader3 also claims
        vm.prank(trader3);
        (uint256 winnings3,) = market.redeemOutcome(0, 200e18);
        assertEq(winnings3, 200e18);

        // 6. Loser tries to claim (gets nothing)
        uint256 trader2FinalBalance = usdc.balanceOf(trader2);

        vm.prank(trader2);
        (uint256 winnings2,) = market.redeemOutcome(1, 300e18);

        assertEq(winnings2, 0);
        assertEq(usdc.balanceOf(trader2), trader2FinalBalance); // No change

        // 7. Creator withdraws accumulated fees
        uint256 fees = market.accumulatedFees();
        assertGt(fees, 0);

        uint256 creatorBalanceBefore = usdc.balanceOf(marketCreator);

        vm.prank(marketCreator);
        market.withdrawFees(marketCreator);

        assertEq(usdc.balanceOf(marketCreator), creatorBalanceBefore + fees);
    }

    /// @notice Test multiple markets with different outcomes
    function test_MultipleMarkets() public {
        TruthyMarket[] memory markets = new TruthyMarket[](3);

        // Create 3 different markets
        for (uint256 i = 0; i < 3; i++) {
            vm.prank(marketCreator);
            markets[i] = factory.createMarket(
                keccak256(abi.encodePacked("market", i)),
                string(abi.encodePacked("Market ", vm.toString(i))),
                "Test market",
                "crypto",
                "url",
                resolver,
                block.timestamp + 30 days,
                [0.5e18, 0.5e18],
                1000e6
            );

            vm.prank(trader1);
            usdc.approve(address(markets[i]), type(uint256).max);
        }

        // Trader1 buys YES in all markets
        for (uint256 i = 0; i < 3; i++) {
            vm.prank(trader1);
            markets[i].buyOutcome(0, 100e18);
        }

        // Resolve markets differently
        vm.warp(block.timestamp + 30 days + 1);

        vm.startPrank(resolver);
        markets[0].resolve(0); // YES wins
        markets[1].resolve(1); // NO wins
        markets[2].resolve(0); // YES wins
        vm.stopPrank();

        // Trader1 claims from all markets
        uint256 totalWinnings = 0;

        for (uint256 i = 0; i < 3; i++) {
            vm.prank(trader1);
            (uint256 winnings,) = markets[i].redeemOutcome(0, 100e18);
            totalWinnings += winnings;
        }

        // Should win 2 out of 3
        assertEq(totalWinnings, 200e18);
    }

    /// @notice Test market with heavy trading activity
    function test_HighVolumeTrading() public {
        vm.prank(marketCreator);
        TruthyMarket market = factory.createMarket(
            keccak256("high-volume"),
            "High Volume Test",
            "Test",
            "crypto",
            "url",
            resolver,
            block.timestamp + 30 days,
            [0.5e18, 0.5e18],
            5000e6 // High initial liquidity
        );

        // Approve market for all traders
        address[3] memory traders = [trader1, trader2, trader3];
        for (uint256 i = 0; i < traders.length; i++) {
            vm.prank(traders[i]);
            usdc.approve(address(market), type(uint256).max);

            // Mint extra USDC for heavy trading
            usdc.mint(traders[i], 50000e6);
        }

        // Simulate heavy trading
        for (uint256 round = 0; round < 5; round++) {
            // Each trader buys and sells multiple times
            for (uint256 i = 0; i < traders.length; i++) {
                vm.prank(traders[i]);
                market.buyOutcome(i % 2, 100e18); // Alternate between YES and NO

                if (round > 0) {
                    vm.prank(traders[i]);
                    market.redeemOutcome(i % 2, 50e18); // Sell some
                }
            }
        }

        // Verify high volume
        uint256 totalVolume = market.totalVolume();
        assertGt(totalVolume, 1000e6); // Should have significant volume

        // Verify all user volumes tracked
        for (uint256 i = 0; i < traders.length; i++) {
            assertGt(market.userVolume(traders[i]), 0);
        }
    }

    /// @notice Test price discovery through trading
    function test_PriceDiscovery() public {
        vm.prank(marketCreator);
        TruthyMarket market = factory.createMarket(
            keccak256("price-discovery"),
            "Price Discovery Test",
            "Test",
            "crypto",
            "url",
            resolver,
            block.timestamp + 30 days,
            [0.5e18, 0.5e18], // Start 50/50
            2000e6
        );

        vm.prank(trader1);
        usdc.approve(address(market), type(uint256).max);
        usdc.mint(trader1, 100000e6);

        // Initial price
        uint256 initialYesPrice = market.getOutcomePrice(0);
        assertEq(initialYesPrice, 0.5e18);

        // Heavy buying of YES
        for (uint256 i = 0; i < 5; i++) {
            vm.prank(trader1);
            market.buyOutcome(0, 500e18);
        }

        // YES price should increase significantly
        uint256 finalYesPrice = market.getOutcomePrice(0);
        assertGt(finalYesPrice, initialYesPrice);
        assertGt(finalYesPrice, 0.7e18); // Should be > 70%

        // NO price should decrease
        uint256 finalNoPrice = market.getOutcomePrice(1);
        assertLt(finalNoPrice, 0.3e18); // Should be < 30%

        // Prices should sum to ~100%
        assertApproxEqAbs(finalYesPrice + finalNoPrice, 1e18, 1e15); // Within 0.1%
    }

    /// @notice Test fee accumulation across multiple trades
    function test_FeeAccumulation() public {
        vm.prank(marketCreator);
        TruthyMarket market = factory.createMarket(
            keccak256("fee-test"), "Fee Test", "Test", "crypto", "url", resolver, block.timestamp + 30 days, [0.5e18, 0.5e18], 1000e6
        );

        vm.prank(trader1);
        usdc.approve(address(market), type(uint256).max);
        usdc.mint(trader1, 100000e6);

        uint256 initialFees = market.accumulatedFees();

        // Multiple trades
        for (uint256 i = 0; i < 10; i++) {
            vm.prank(trader1);
            market.buyOutcome(i % 2, 100e18);
        }

        uint256 feesAfterBuys = market.accumulatedFees();
        assertGt(feesAfterBuys, initialFees);

        // Sell some
        for (uint256 i = 0; i < 5; i++) {
            vm.prank(trader1);
            market.redeemOutcome(i % 2, 50e18);
        }

        uint256 feesAfterSells = market.accumulatedFees();
        assertGt(feesAfterSells, feesAfterBuys);

        // Factory should accumulate creation fees
        uint256 factoryFees = factory.accumulatedFees();
        assertGt(factoryFees, 0);
    }

    /// @notice Test edge case: market created and immediately resolved
    function test_QuickResolve() public {
        vm.prank(marketCreator);
        TruthyMarket market = factory.createMarket(
            keccak256("quick-resolve"),
            "Quick Resolve",
            "Test",
            "crypto",
            "url",
            resolver,
            block.timestamp + 1 hours,
            [0.5e18, 0.5e18],
            1000e6
        );

        // Warp to expiry
        vm.warp(block.timestamp + 1 hours + 1);

        // Resolve immediately
        vm.prank(resolver);
        market.resolve(0);

        assertTrue(market.isResolved());

        // Should still be able to claim initial liquidity
        // (though no one traded)
    }

    /// @notice Test recovery from paused state
    function test_PauseAndRecovery() public {
        vm.prank(marketCreator);
        TruthyMarket market = factory.createMarket(
            keccak256("pause-test"), "Pause Test", "Test", "crypto", "url", resolver, block.timestamp + 30 days, [0.5e18, 0.5e18], 1000e6
        );

        vm.prank(trader1);
        usdc.approve(address(market), type(uint256).max);

        // Pause market
        vm.prank(marketCreator);
        market.pause();

        // Trading should fail
        vm.prank(trader1);
        vm.expectRevert();
        market.buyOutcome(0, 100e18);

        // Unpause
        vm.prank(marketCreator);
        market.unpause();

        // Trading should work again
        vm.prank(trader1);
        market.buyOutcome(0, 100e18);

        assertEq(market.getOutcomeToken(0).balanceOf(trader1), 100e18);
    }
}
