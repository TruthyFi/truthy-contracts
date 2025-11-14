// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.20;

import {Script, console} from "forge-std/Script.sol";
import {TruthyMarketFactory} from "../src/TruthyMarketFactory.sol";
import {TruthyMarket} from "../src/TruthyMarket.sol";
import {IERC20} from "@openzeppelin/contracts/token/ERC20/IERC20.sol";

/// @title WithdrawFees
/// @notice Script to withdraw accumulated fees from factory and markets
/// @dev Allows batch withdrawal of fees from all markets
contract WithdrawFees is Script {
    function run() external {
        uint256 ownerPrivateKey = vm.envUint("PRIVATE_KEY");
        address factoryAddress = vm.envAddress("FACTORY_ADDRESS");
        address usdcAddress = vm.envAddress("USDC_ADDRESS");
        address recipient = vm.envAddress("FEE_RECIPIENT");

        TruthyMarketFactory factory = TruthyMarketFactory(factoryAddress);
        IERC20 usdc = IERC20(usdcAddress);

        console.log("========================================");
        console.log("FEE WITHDRAWAL");
        console.log("========================================");
        console.log("Factory:", factoryAddress);
        console.log("Recipient:", recipient);
        console.log("Operator:", vm.addr(ownerPrivateKey));
        console.log("");

        uint256 recipientBalanceBefore = usdc.balanceOf(recipient);

        vm.startBroadcast(ownerPrivateKey);

        // Withdraw factory fees
        uint256 factoryFees = factory.accumulatedFees();
        console.log("=== Factory Fees ===");
        console.log("Accumulated:", factoryFees, "USDC");

        if (factoryFees > 0) {
            try factory.withdrawFees(recipient) {
                console.log("✅ Factory fees withdrawn");
            } catch Error(string memory reason) {
                console.log("❌ Failed to withdraw factory fees:", reason);
            }
        } else {
            console.log("No factory fees to withdraw");
        }

        // Withdraw fees from all markets
        address[] memory markets = factory.getAllMarkets();
        console.log("\n=== Market Fees ===");
        console.log("Total markets:", markets.length);

        uint256 totalMarketFees = 0;
        uint256 withdrawnCount = 0;
        uint256 failedCount = 0;

        for (uint256 i = 0; i < markets.length; i++) {
            TruthyMarket market = TruthyMarket(markets[i]);
            uint256 marketFees = market.accumulatedFees();

            if (marketFees > 0) {
                console.log("\nMarket:", market.name());
                console.log("  Fees:", marketFees, "USDC");

                try market.withdrawFees(recipient) {
                    console.log("  ✅ Withdrawn");
                    totalMarketFees += marketFees;
                    withdrawnCount++;
                } catch Error(string memory reason) {
                    console.log("  ❌ Failed:", reason);
                    failedCount++;
                }
            }
        }

        vm.stopBroadcast();

        uint256 recipientBalanceAfter = usdc.balanceOf(recipient);
        uint256 totalWithdrawn = recipientBalanceAfter - recipientBalanceBefore;

        console.log("\n========================================");
        console.log("WITHDRAWAL SUMMARY");
        console.log("========================================");
        console.log("Factory Fees:", factoryFees, "USDC");
        console.log("Market Fees:", totalMarketFees, "USDC");
        console.log("Total Withdrawn:", totalWithdrawn, "USDC");
        console.log("Markets Processed:", withdrawnCount);
        console.log("Failed Withdrawals:", failedCount);
        console.log("");
        console.log("Recipient Balance Before:", recipientBalanceBefore, "USDC");
        console.log("Recipient Balance After:", recipientBalanceAfter, "USDC");

        if (failedCount == 0) {
            console.log("\n✅ ALL FEES WITHDRAWN SUCCESSFULLY");
        } else {
            console.log("\n⚠️  SOME WITHDRAWALS FAILED - REVIEW REQUIRED");
        }
    }
}
