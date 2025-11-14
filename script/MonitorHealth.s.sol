// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.20;

import {Script, console} from "forge-std/Script.sol";
import {TruthyMarketFactory} from "../src/TruthyMarketFactory.sol";
import {TruthyMarket} from "../src/TruthyMarket.sol";
import {IERC20} from "@openzeppelin/contracts/token/ERC20/IERC20.sol";

/// @title MonitorHealth
/// @notice Script to monitor the health and status of deployed contracts
/// @dev Run periodically to check contract health
contract MonitorHealth is Script {
    TruthyMarketFactory public factory;
    IERC20 public usdc;

    function run() external view {
        address factoryAddress = vm.envAddress("FACTORY_ADDRESS");
        address usdcAddress = vm.envAddress("USDC_ADDRESS");

        factory = TruthyMarketFactory(factoryAddress);
        usdc = IERC20(usdcAddress);

        console.log("========================================");
        console.log("TRUTHY PLATFORM HEALTH MONITOR");
        console.log("========================================");
        console.log("Timestamp:", block.timestamp);
        console.log("Block Number:", block.number);
        console.log("");

        displayFactoryHealth();
        displayMarketHealth();
        displayFinancialMetrics();
        displayUserActivity();
        displayAlerts();

        console.log("\n========================================");
        console.log("Health check completed at", block.timestamp);
        console.log("========================================");
    }

    function displayFactoryHealth() internal view {
        console.log("=== Factory Health ===");

        uint256 totalMarkets = factory.getTotalMarkets();
        uint256 accumulatedFees = factory.accumulatedFees();

        console.log("Total Markets Created:", totalMarkets);
        console.log("Factory Accumulated Fees:", accumulatedFees, "USDC");
        console.log("Factory Owner:", factory.owner());
        console.log("Creation Fee:", factory.creationFee(), "USDC");
        console.log("Protocol Fee Rate:", factory.protocolFeeRate(), "bps");

        if (totalMarkets == 0) {
            console.log("⚠️  No markets created yet");
        }
    }

    function displayMarketHealth() internal view {
        console.log("\n=== Market Health ===");

        address[] memory markets = factory.getAllMarkets();
        uint256 totalMarkets = markets.length;

        if (totalMarkets == 0) {
            console.log("No markets to monitor");
            return;
        }

        uint256 activeMarkets = 0;
        uint256 resolvedMarkets = 0;
        uint256 expiredMarkets = 0;
        uint256 totalLiquidity = 0;
        uint256 totalVolume = 0;

        for (uint256 i = 0; i < markets.length; i++) {
            TruthyMarket market = TruthyMarket(markets[i]);

            if (market.isResolved()) {
                resolvedMarkets++;
            } else if (block.timestamp > market.expiresAt()) {
                expiredMarkets++;
            } else {
                activeMarkets++;
            }

            totalLiquidity += market.getTotalLiquidity();
            totalVolume += market.totalVolume();
        }

        console.log("Total Markets:", totalMarkets);
        console.log("Active Markets:", activeMarkets);
        console.log("Expired (Unresolved):", expiredMarkets);
        console.log("Resolved Markets:", resolvedMarkets);
        console.log("Total Liquidity:", totalLiquidity, "USDC");
        console.log("Total Volume:", totalVolume, "USDC");

        if (expiredMarkets > 0) {
            console.log("⚠️ ", expiredMarkets, "markets need resolution");
        }
    }

    function displayFinancialMetrics() internal view {
        console.log("\n=== Financial Metrics ===");

        address[] memory markets = factory.getAllMarkets();

        if (markets.length == 0) {
            console.log("No financial data available yet");
            return;
        }

        uint256 totalFeesCollected = factory.accumulatedFees();
        uint256 totalMarketFees = 0;

        for (uint256 i = 0; i < markets.length; i++) {
            TruthyMarket market = TruthyMarket(markets[i]);
            totalMarketFees += market.accumulatedFees();
        }

        uint256 factoryBalance = usdc.balanceOf(address(factory));

        console.log("Factory Fees Collected:", totalFeesCollected, "USDC");
        console.log("Market Fees (All):", totalMarketFees, "USDC");
        console.log("Factory USDC Balance:", factoryBalance, "USDC");
        console.log("Total Protocol Revenue:", totalFeesCollected + totalMarketFees, "USDC");
    }

    function displayUserActivity() internal view {
        console.log("\n=== User Activity ===");

        address[] memory markets = factory.getAllMarkets();

        if (markets.length == 0) {
            console.log("No user activity data available yet");
            return;
        }

        // Find most active market
        uint256 highestVolume = 0;
        address mostActiveMarket = address(0);
        string memory mostActiveMarketName = "";

        for (uint256 i = 0; i < markets.length; i++) {
            TruthyMarket market = TruthyMarket(markets[i]);
            uint256 volume = market.totalVolume();

            if (volume > highestVolume) {
                highestVolume = volume;
                mostActiveMarket = markets[i];
                mostActiveMarketName = market.name();
            }
        }

        if (mostActiveMarket != address(0)) {
            console.log("Most Active Market:", mostActiveMarket);
            console.log("Name:", mostActiveMarketName);
            console.log("Volume:", highestVolume, "USDC");
        }
    }

    function displayAlerts() internal view {
        console.log("\n=== System Alerts ===");

        address[] memory markets = factory.getAllMarkets();
        bool hasAlerts = false;

        // Check for expired markets needing resolution
        for (uint256 i = 0; i < markets.length; i++) {
            TruthyMarket market = TruthyMarket(markets[i]);

            if (!market.isResolved() && block.timestamp > market.expiresAt()) {
                if (!hasAlerts) {
                    console.log("\n⚠️  ALERTS:");
                    hasAlerts = true;
                }
                console.log("Market needs resolution:", market.name());
                console.log("  Address:", address(market));
                console.log("  Expired:", market.expiresAt());
            }
        }

        // Check for low liquidity markets
        for (uint256 i = 0; i < markets.length; i++) {
            TruthyMarket market = TruthyMarket(markets[i]);

            if (!market.isResolved() && market.getTotalLiquidity() < 100e6) {
                if (!hasAlerts) {
                    console.log("\n⚠️  ALERTS:");
                    hasAlerts = true;
                }
                console.log("Low liquidity market:", market.name());
                console.log("  Liquidity:", market.getTotalLiquidity(), "USDC");
            }
        }

        if (!hasAlerts) {
            console.log("✅ No alerts - all systems healthy");
        }
    }
}
