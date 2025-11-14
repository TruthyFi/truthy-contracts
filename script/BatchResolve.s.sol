// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.20;

import {Script, console} from "forge-std/Script.sol";
import {TruthyMarketFactory} from "../src/TruthyMarketFactory.sol";
import {TruthyMarket} from "../src/TruthyMarket.sol";

/// @title BatchResolve
/// @notice Script to batch resolve multiple expired markets
/// @dev Useful for resolvers to efficiently process multiple markets
contract BatchResolve is Script {
    struct MarketToResolve {
        address marketAddress;
        string name;
        uint256 expiresAt;
        uint256 winningOutcome;
    }

    function run() external {
        uint256 resolverPrivateKey = vm.envUint("PRIVATE_KEY");
        address factoryAddress = vm.envAddress("FACTORY_ADDRESS");

        TruthyMarketFactory factory = TruthyMarketFactory(factoryAddress);

        console.log("========================================");
        console.log("BATCH MARKET RESOLUTION");
        console.log("========================================");
        console.log("Factory:", factoryAddress);
        console.log("Resolver:", vm.addr(resolverPrivateKey));
        console.log("");

        // Find all expired unresolved markets
        address[] memory allMarkets = factory.getAllMarkets();
        MarketToResolve[] memory expiredMarkets = new MarketToResolve[](allMarkets.length);
        uint256 expiredCount = 0;

        console.log("Scanning for expired markets...");

        for (uint256 i = 0; i < allMarkets.length; i++) {
            TruthyMarket market = TruthyMarket(allMarkets[i]);

            if (!market.isResolved() && block.timestamp > market.expiresAt()) {
                expiredMarkets[expiredCount] = MarketToResolve({
                    marketAddress: allMarkets[i],
                    name: market.name(),
                    expiresAt: market.expiresAt(),
                    winningOutcome: 0 // Will be set manually
                });
                expiredCount++;

                console.log("\nFound expired market #", expiredCount);
                console.log("  Address:", allMarkets[i]);
                console.log("  Name:", market.name());
                console.log("  Expired:", market.expiresAt());
                console.log("  Current YES price:", market.getOutcomePrice(0));
                console.log("  Current NO price:", market.getOutcomePrice(1));
            }
        }

        if (expiredCount == 0) {
            console.log("\n✅ No expired markets found - all up to date!");
            return;
        }

        console.log("\n========================================");
        console.log("Found", expiredCount, "expired markets needing resolution");
        console.log("========================================");
        console.log("\n⚠️  MANUAL STEP REQUIRED:");
        console.log("Review each market and determine the winning outcome");
        console.log("Then modify this script to set winningOutcome for each market");
        console.log("\nExample:");
        console.log('expiredMarkets[0].winningOutcome = 0; // YES wins');
        console.log('expiredMarkets[1].winningOutcome = 1; // NO wins');
        console.log("\n⚠️  Uncomment the resolution code below after setting outcomes");

        // UNCOMMENT AND MODIFY THE CODE BELOW AFTER DETERMINING OUTCOMES
        /*
        vm.startBroadcast(resolverPrivateKey);

        uint256 resolvedCount = 0;
        uint256 failedCount = 0;

        for (uint256 i = 0; i < expiredCount; i++) {
            TruthyMarket market = TruthyMarket(expiredMarkets[i].marketAddress);

            console.log("\nResolving:", expiredMarkets[i].name);
            console.log("  Outcome:", expiredMarkets[i].winningOutcome);

            try market.resolve(expiredMarkets[i].winningOutcome) {
                console.log("  ✅ Resolved successfully");
                resolvedCount++;
            } catch Error(string memory reason) {
                console.log("  ❌ Failed:", reason);
                failedCount++;
            } catch {
                console.log("  ❌ Failed: Unknown error");
                failedCount++;
            }
        }

        vm.stopBroadcast();

        console.log("\n========================================");
        console.log("RESOLUTION SUMMARY");
        console.log("========================================");
        console.log("Total Expired:", expiredCount);
        console.log("Successfully Resolved:", resolvedCount);
        console.log("Failed:", failedCount);

        if (resolvedCount == expiredCount) {
            console.log("\n✅ ALL MARKETS RESOLVED SUCCESSFULLY");
        }
        */
    }
}
