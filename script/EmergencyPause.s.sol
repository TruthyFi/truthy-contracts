// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.20;

import {Script, console} from "forge-std/Script.sol";
import {TruthyMarketFactory} from "../src/TruthyMarketFactory.sol";
import {TruthyMarket} from "../src/TruthyMarket.sol";

/// @title EmergencyPause
/// @notice Emergency script to pause markets or factory in case of security issues
/// @dev Only use in emergencies - requires owner access
contract EmergencyPause is Script {
    function run() external {
        uint256 ownerPrivateKey = vm.envUint("PRIVATE_KEY");
        address factoryAddress = vm.envAddress("FACTORY_ADDRESS");

        TruthyMarketFactory factory = TruthyMarketFactory(factoryAddress);

        console.log("========================================");
        console.log("EMERGENCY PAUSE PROCEDURE");
        console.log("========================================");
        console.log("Factory:", factoryAddress);
        console.log("Operator:", vm.addr(ownerPrivateKey));
        console.log("");

        vm.startBroadcast(ownerPrivateKey);

        // Get all markets
        address[] memory markets = factory.getAllMarkets();
        console.log("Total markets to pause:", markets.length);

        uint256 pausedCount = 0;
        uint256 failedCount = 0;

        // Pause all active markets
        for (uint256 i = 0; i < markets.length; i++) {
            TruthyMarket market = TruthyMarket(markets[i]);

            try market.pause() {
                console.log("✅ Paused market:", address(market));
                console.log("   Name:", market.name());
                pausedCount++;
            } catch {
                console.log("❌ Failed to pause market:", address(market));
                failedCount++;
            }
        }

        vm.stopBroadcast();

        console.log("\n========================================");
        console.log("PAUSE SUMMARY");
        console.log("========================================");
        console.log("Total Markets:", markets.length);
        console.log("Successfully Paused:", pausedCount);
        console.log("Failed:", failedCount);

        if (pausedCount == markets.length) {
            console.log("\n✅ ALL MARKETS PAUSED SUCCESSFULLY");
        } else if (failedCount > 0) {
            console.log("\n⚠️  SOME MARKETS FAILED TO PAUSE - MANUAL INTERVENTION REQUIRED");
        }

        console.log("\n⚠️  IMPORTANT: Document the reason for this emergency pause!");
        console.log("⚠️  To unpause, use the EmergencyUnpause script or call unpause() on each market");
    }
}
