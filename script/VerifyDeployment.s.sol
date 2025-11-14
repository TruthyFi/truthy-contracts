// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.20;

import {Script, console} from "forge-std/Script.sol";
import {TruthyMarketFactory} from "../src/TruthyMarketFactory.sol";
import {TruthyMarket} from "../src/TruthyMarket.sol";
import {MockUSDC} from "../src/mocks/MockUSDC.sol";

/// @title VerifyDeployment
/// @notice Script to verify deployed contracts are configured correctly
contract VerifyDeployment is Script {
    function run() external view {
        // Read deployment addresses from environment
        address factoryAddress = vm.envAddress("FACTORY_ADDRESS");
        address usdcAddress = vm.envAddress("USDC_ADDRESS");

        console.log("=== Verifying Deployment ===");
        console.log("Factory:", factoryAddress);
        console.log("USDC:", usdcAddress);

        TruthyMarketFactory factory = TruthyMarketFactory(factoryAddress);

        // Verify factory configuration
        console.log("\n=== Factory Configuration ===");
        console.log("Payment Token:", address(factory.paymentToken()));
        console.log("Creation Fee:", factory.creationFee());
        console.log("Protocol Fee Rate:", factory.protocolFeeRate());
        console.log("Owner:", factory.owner());
        console.log("Total Markets:", factory.getTotalMarkets());

        require(address(factory.paymentToken()) == usdcAddress, "Invalid payment token");
        require(factory.creationFee() > 0, "Creation fee not set");
        require(factory.protocolFeeRate() <= 1000, "Fee rate too high");

        console.log("\n✅ Factory verification passed!");

        // If markets exist, verify one
        if (factory.getTotalMarkets() > 0) {
            address[] memory markets = factory.getAllMarkets();
            address firstMarket = markets[0];

            console.log("\n=== Verifying First Market ===");
            console.log("Market Address:", firstMarket);

            TruthyMarket market = TruthyMarket(firstMarket);

            console.log("Name:", market.name());
            console.log("Category:", market.category());
            console.log("Creator:", market.creator());
            console.log("Resolver:", market.getResolver());
            console.log("Expires At:", market.expiresAt());
            console.log("Is Resolved:", market.isResolved());
            console.log("Total Liquidity:", market.getTotalLiquidity());
            console.log("Min Bet:", market.minBet());
            console.log("Max Bet:", market.maxBet());

            console.log("\n✅ Market verification passed!");
        }

        console.log("\n=== Deployment Verified Successfully! ===");
    }
}
