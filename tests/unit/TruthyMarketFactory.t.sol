// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.20;

import {Test, console} from "forge-std/Test.sol";
import {TruthyMarketFactory} from "../../src/TruthyMarketFactory.sol";
import {TruthyMarket} from "../../src/TruthyMarket.sol";
import {MockUSDC} from "../../src/mocks/MockUSDC.sol";
import {Constants} from "../../src/libraries/Constants.sol";

/// @title TruthyMarketFactoryTest
/// @notice Unit tests for TruthyMarketFactory
contract TruthyMarketFactoryTest is Test {
    TruthyMarketFactory public factory;
    MockUSDC public usdc;

    address public owner = address(this);
    address public creator = address(0x1);
    address public resolver = address(0x2);

    uint256 public constant CREATION_FEE = 5e6; // 5 USDC
    uint256 public constant PROTOCOL_FEE_RATE = 200; // 2%

    function setUp() public {
        usdc = new MockUSDC();
        factory = new TruthyMarketFactory(address(usdc), CREATION_FEE, PROTOCOL_FEE_RATE);

        // Setup creator with USDC
        usdc.mint(creator, 10000e6);
        vm.prank(creator);
        usdc.approve(address(factory), type(uint256).max);
    }

    // ============ Constructor Tests ============

    function test_Constructor() public {
        assertEq(address(factory.paymentToken()), address(usdc));
        assertEq(factory.creationFee(), CREATION_FEE);
        assertEq(factory.protocolFeeRate(), PROTOCOL_FEE_RATE);
        assertEq(factory.owner(), owner);
    }

    function testFail_ConstructorInvalidToken() public {
        new TruthyMarketFactory(address(0), CREATION_FEE, PROTOCOL_FEE_RATE);
    }

    function testFail_ConstructorFeeRateTooHigh() public {
        new TruthyMarketFactory(address(usdc), CREATION_FEE, 1001); // > 10%
    }

    // ============ Market Creation Tests ============

    function test_CreateMarket() public {
        bytes32 marketId = keccak256("test-market");
        uint256 creatorBalanceBefore = usdc.balanceOf(creator);

        vm.prank(creator);
        TruthyMarket market = factory.createMarket(
            marketId,
            "Test Market",
            "Test Description",
            "crypto",
            "https://twitter.com/test",
            resolver,
            block.timestamp + 30 days,
            [0.5e18, 0.5e18],
            1000e6
        );

        // Verify market created
        assertTrue(factory.marketExists(marketId));
        assertEq(factory.getMarket(marketId), address(market));
        assertEq(factory.getTotalMarkets(), 1);

        // Verify fee collected
        assertEq(usdc.balanceOf(creator), creatorBalanceBefore - CREATION_FEE - 1000e6);
        assertEq(factory.accumulatedFees(), CREATION_FEE);

        // Verify market metadata
        assertEq(market.id(), marketId);
        assertEq(market.name(), "Test Market");
        assertEq(market.creator(), creator);
        assertEq(market.getResolver(), resolver);
    }

    function test_CreateMarketWithoutInitialLiquidity() public {
        bytes32 marketId = keccak256("test-market");

        vm.prank(creator);
        TruthyMarket market = factory.createMarket(
            marketId,
            "Test Market",
            "Test Description",
            "crypto",
            "https://twitter.com/test",
            resolver,
            block.timestamp + 30 days,
            [0.5e18, 0.5e18],
            0 // No initial liquidity
        );

        assertTrue(address(market) != address(0));
        assertEq(market.getTotalLiquidity(), 0);
    }

    function testFail_CreateDuplicateMarket() public {
        bytes32 marketId = keccak256("test-market");

        vm.startPrank(creator);
        factory.createMarket(
            marketId, "Test Market", "Description", "crypto", "url", resolver, block.timestamp + 30 days, [0.5e18, 0.5e18], 0
        );

        // Try to create again with same ID
        factory.createMarket(
            marketId, "Test Market", "Description", "crypto", "url", resolver, block.timestamp + 30 days, [0.5e18, 0.5e18], 0
        );
        vm.stopPrank();
    }

    function testFail_CreateMarketExpiredDate() public {
        vm.prank(creator);
        factory.createMarket(
            keccak256("test"),
            "Test",
            "Description",
            "crypto",
            "url",
            resolver,
            block.timestamp - 1, // Past expiry
            [0.5e18, 0.5e18],
            0
        );
    }

    function testFail_CreateMarketEmptyName() public {
        vm.prank(creator);
        factory.createMarket(
            keccak256("test"), "", "Description", "crypto", "url", resolver, block.timestamp + 30 days, [0.5e18, 0.5e18], 0
        );
    }

    function testFail_CreateMarketInvalidResolver() public {
        vm.prank(creator);
        factory.createMarket(
            keccak256("test"),
            "Test",
            "Description",
            "crypto",
            "url",
            address(0), // Invalid resolver
            block.timestamp + 30 days,
            [0.5e18, 0.5e18],
            0
        );
    }

    // ============ Query Tests ============

    function test_GetAllMarkets() public {
        // Create multiple markets
        for (uint256 i = 0; i < 3; i++) {
            vm.prank(creator);
            factory.createMarket(
                keccak256(abi.encodePacked("market", i)),
                "Test Market",
                "Description",
                "crypto",
                "url",
                resolver,
                block.timestamp + 30 days,
                [0.5e18, 0.5e18],
                0
            );
        }

        address[] memory markets = factory.getAllMarkets();
        assertEq(markets.length, 3);
    }

    function test_GetMarketsByCreator() public {
        address creator2 = address(0x3);
        usdc.mint(creator2, 10000e6);
        vm.prank(creator2);
        usdc.approve(address(factory), type(uint256).max);

        // Creator 1 creates 2 markets
        for (uint256 i = 0; i < 2; i++) {
            vm.prank(creator);
            factory.createMarket(
                keccak256(abi.encodePacked("market", i)),
                "Test",
                "Description",
                "crypto",
                "url",
                resolver,
                block.timestamp + 30 days,
                [0.5e18, 0.5e18],
                0
            );
        }

        // Creator 2 creates 1 market
        vm.prank(creator2);
        factory.createMarket(
            keccak256("creator2-market"), "Test", "Description", "crypto", "url", resolver, block.timestamp + 30 days, [0.5e18, 0.5e18], 0
        );

        bytes32[] memory creator1Markets = factory.getMarketsByCreator(creator);
        bytes32[] memory creator2Markets = factory.getMarketsByCreator(creator2);

        assertEq(creator1Markets.length, 2);
        assertEq(creator2Markets.length, 1);
    }

    function test_GetMarketsByCategory() public {
        // Create markets in different categories
        vm.startPrank(creator);
        factory.createMarket(
            keccak256("crypto-market"), "Test", "Description", "crypto", "url", resolver, block.timestamp + 30 days, [0.5e18, 0.5e18], 0
        );
        factory.createMarket(
            keccak256("politics-market"),
            "Test",
            "Description",
            "politics",
            "url",
            resolver,
            block.timestamp + 30 days,
            [0.5e18, 0.5e18],
            0
        );
        factory.createMarket(
            keccak256("crypto-market-2"),
            "Test",
            "Description",
            "crypto",
            "url",
            resolver,
            block.timestamp + 30 days,
            [0.5e18, 0.5e18],
            0
        );
        vm.stopPrank();

        bytes32[] memory cryptoMarkets = factory.getMarketsByCategory("crypto");
        bytes32[] memory politicsMarkets = factory.getMarketsByCategory("politics");

        assertEq(cryptoMarkets.length, 2);
        assertEq(politicsMarkets.length, 1);
    }

    // ============ Admin Tests ============

    function test_SetCreationFee() public {
        uint256 newFee = 10e6;

        factory.setCreationFee(newFee);
        assertEq(factory.creationFee(), newFee);
    }

    function testFail_SetCreationFeeNotOwner() public {
        vm.prank(creator);
        factory.setCreationFee(10e6);
    }

    function test_SetProtocolFeeRate() public {
        uint256 newRate = 300; // 3%

        factory.setProtocolFeeRate(newRate);
        assertEq(factory.protocolFeeRate(), newRate);
    }

    function testFail_SetProtocolFeeRateTooHigh() public {
        factory.setProtocolFeeRate(1001); // > 10%
    }

    function test_WithdrawFees() public {
        // Create a market to generate fees
        vm.prank(creator);
        factory.createMarket(
            keccak256("test"), "Test", "Description", "crypto", "url", resolver, block.timestamp + 30 days, [0.5e18, 0.5e18], 0
        );

        uint256 fees = factory.accumulatedFees();
        assertEq(fees, CREATION_FEE);

        uint256 ownerBalanceBefore = usdc.balanceOf(owner);
        factory.withdrawFees(owner);

        assertEq(usdc.balanceOf(owner), ownerBalanceBefore + fees);
        assertEq(factory.accumulatedFees(), 0);
    }

    function testFail_WithdrawFeesInvalidAddress() public {
        factory.withdrawFees(address(0));
    }

    function testFail_WithdrawNoFees() public {
        factory.withdrawFees(owner);
    }

    // ============ Gas Benchmarks ============

    function testGas_CreateMarket() public {
        vm.prank(creator);
        factory.createMarket(
            keccak256("gas-test"), "Test", "Description", "crypto", "url", resolver, block.timestamp + 30 days, [0.5e18, 0.5e18], 1000e6
        );
    }

    function testGas_CreateMarketNoLiquidity() public {
        vm.prank(creator);
        factory.createMarket(
            keccak256("gas-test"), "Test", "Description", "crypto", "url", resolver, block.timestamp + 30 days, [0.5e18, 0.5e18], 0
        );
    }
}
