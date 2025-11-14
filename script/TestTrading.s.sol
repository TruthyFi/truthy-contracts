// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.20;

import {Script, console} from "forge-std/Script.sol";
import {TruthyMarketFactory} from "../src/TruthyMarketFactory.sol";
import {TruthyMarket} from "../src/TruthyMarket.sol";
import {MockUSDC} from "../src/mocks/MockUSDC.sol";

/// @title TestTrading
/// @notice Interactive script to test trading on deployed contracts
contract TestTrading is Script {
    function run() external {
        uint256 deployerPrivateKey = vm.envUint("PRIVATE_KEY");
        address deployer = vm.addr(deployerPrivateKey);

        address factoryAddress = vm.envAddress("FACTORY_ADDRESS");
        address usdcAddress = vm.envAddress("USDC_ADDRESS");

        TruthyMarketFactory factory = TruthyMarketFactory(factoryAddress);
        MockUSDC usdc = MockUSDC(usdcAddress);

        console.log("=== Testing Trading ===");
        console.log("Trader:", deployer);
        console.log("USDC Balance:", usdc.balanceOf(deployer));

        vm.startBroadcast(deployerPrivateKey);

        // Get test USDC if on testnet
        if (block.chainid == 84532) {
            // Base Sepolia
            console.log("\nCalling faucet for test USDC...");
            usdc.faucet();
            console.log("New USDC Balance:", usdc.balanceOf(deployer));
        }

        // Get first market
        address[] memory markets = factory.getAllMarkets();
        require(markets.length > 0, "No markets available");

        address marketAddress = markets[0];
        TruthyMarket market = TruthyMarket(marketAddress);

        console.log("\n=== Market Info ===");
        console.log("Market:", marketAddress);
        console.log("Name:", market.name());
        console.log("YES Price:", market.getOutcomePrice(0));
        console.log("NO Price:", market.getOutcomePrice(1));

        // Approve market to spend USDC
        console.log("\nApproving USDC...");
        usdc.approve(marketAddress, type(uint256).max);

        // Buy YES outcome
        uint256 buyAmount = 10e18; // 10 outcome tokens
        console.log("\nBuying", buyAmount / 1e18, "YES tokens...");

        uint256 costPreview = market.previewCostToBuy(0, buyAmount);
        console.log("Estimated cost:", costPreview);

        (uint256 actualCost, uint256 fee) = market.buyOutcome(0, buyAmount);

        console.log("Actual cost:", actualCost);
        console.log("Fee paid:", fee);
        console.log("YES tokens received:", market.getOutcomeToken(0).balanceOf(deployer));

        // Check updated price
        console.log("\n=== Updated Prices ===");
        console.log("YES Price:", market.getOutcomePrice(0));
        console.log("NO Price:", market.getOutcomePrice(1));

        vm.stopBroadcast();

        console.log("\n✅ Trading test completed successfully!");
    }
}
