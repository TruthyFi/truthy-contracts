// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.20;

import {Script, console} from "forge-std/Script.sol";
import {TruthyMarketFactory} from "../src/TruthyMarketFactory.sol";
import {TruthyMarket} from "../src/TruthyMarket.sol";

/// @title EmergencyUnpause
/// @notice Script to unpause markets after emergency is resolved
/// @dev Only use after confirming the security issue is resolved
contract EmergencyUnpause is Script {
    function run() external {
        uint256 ownerPrivateKey = vm.envUint("PRIVATE_KEY");
        address factoryAddress = vm.envAddress("FACTORY_ADDRESS");

        TruthyMarketFactory factory = TruthyMarketFactory(factoryAddress);

        console.log("========================================");
        console.log("EMERGENCY UNPAUSE PROCEDURE");
        console.log("========================================");
        console.log("Factory:", factoryAddress);
        console.log("Operator:", vm.addr(ownerPrivateKey));
        console.log("");

        console.log("⚠️  WARNING: Only proceed if:");
        console.log("    1. Security issue has been identified and fixed");
        console.log("    2. Contracts have been re-audited if necessary");
        console.log("    3. All stakeholders have been notified");
        console.log("");

        vm.startBroadcast(ownerPrivateKey);

        // Get all markets
        address[] memory markets = factory.getAllMarkets();
        console.log("Total markets to unpause:", markets.length);

        uint256 unpausedCount = 0;
        uint256 failedCount = 0;

        // Unpause all markets
        for (uint256 i = 0; i < markets.length; i++) {
            TruthyMarket market = TruthyMarket(markets[i]);

            try market.unpause() {
                console.log("✅ Unpaused market:", address(market));
                console.log("   Name:", market.name());
                unpausedCount++;
            } catch {
                console.log("❌ Failed to unpause market:", address(market));
                failedCount++;
            }
        }

        vm.stopBroadcast();

        console.log("\n========================================");
        console.log("UNPAUSE SUMMARY");
        console.log("========================================");
        console.log("Total Markets:", markets.length);
        console.log("Successfully Unpaused:", unpausedCount);
        console.log("Failed:", failedCount);

        if (unpausedCount == markets.length) {
            console.log("\n✅ ALL MARKETS UNPAUSED - TRADING RESUMED");
        } else if (failedCount > 0) {
            console.log("\n⚠️  SOME MARKETS FAILED TO UNPAUSE - MANUAL INTERVENTION REQUIRED");
        }

        console.log("\n📝 Document this recovery in your incident log");
    }
}
