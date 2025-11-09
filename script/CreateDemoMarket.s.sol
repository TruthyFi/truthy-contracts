// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.20;

import {Script, console} from "forge-std/Script.sol";
import {TruthyMarketFactory} from "../src/TruthyMarketFactory.sol";
import {TruthyMarket} from "../src/TruthyMarket.sol";
import {MockUSDC} from "../src/mocks/MockUSDC.sol";

contract CreateDemoMarketScript is Script {
    function run() external {
        uint256 deployerPrivateKey = vm.envUint("PRIVATE_KEY");
        address deployer = vm.addr(deployerPrivateKey);

        // Read deployment addresses (you'll need to set these)
        address factoryAddress = vm.envAddress("FACTORY_ADDRESS");
        address usdcAddress = vm.envAddress("USDC_ADDRESS");

        TruthyMarketFactory factory = TruthyMarketFactory(factoryAddress);
        MockUSDC usdc = MockUSDC(usdcAddress);

        console.log("Creating demo markets from:", deployer);

        vm.startBroadcast(deployerPrivateKey);

        // Mint USDC if using mock
        if (block.chainid != 8453) {
            usdc.mint(deployer, 10000e6); // 10,000 USDC
            console.log("Minted 10,000 USDC to deployer");
        }

        // Approve factory
        usdc.approve(address(factory), type(uint256).max);

        // Demo Market 1: ETH Price Prediction
        bytes32 marketId1 = keccak256("eth-5000-2024");
        TruthyMarket market1 = factory.createMarket(
            marketId1,
            "Will ETH reach $5,000 by end of 2024?",
            "Prediction market for Ethereum price reaching $5,000 USD by December 31, 2024",
            "crypto",
            "https://twitter.com/demo/eth-prediction",
            deployer, // resolver (you can change this)
            block.timestamp + 60 days,
            [0.3e18, 0.7e18], // 30% YES, 70% NO initial prices
            1000e6 // 1000 USDC initial liquidity
        );
        console.log("Market 1 created at:", address(market1));

        // Demo Market 2: US Election
        bytes32 marketId2 = keccak256("us-election-2024");
        TruthyMarket market2 = factory.createMarket(
            marketId2,
            "Will Trump win the 2024 US Presidential Election?",
            "Binary prediction market for 2024 US Presidential Election outcome",
            "politics",
            "https://twitter.com/demo/election",
            deployer,
            block.timestamp + 90 days,
            [0.5e18, 0.5e18], // 50/50
            500e6 // 500 USDC
        );
        console.log("Market 2 created at:", address(market2));

        // Demo Market 3: Bitcoin Halving
        bytes32 marketId3 = keccak256("btc-100k-2024");
        TruthyMarket market3 = factory.createMarket(
            marketId3,
            "Will Bitcoin reach $100k before 2025?",
            "Will BTC price hit $100,000 USD before January 1, 2025?",
            "crypto",
            "https://twitter.com/demo/btc",
            deployer,
            block.timestamp + 45 days,
            [0.6e18, 0.4e18], // 60% YES, 40% NO
            2000e6 // 2000 USDC
        );
        console.log("Market 3 created at:", address(market3));

        // Demo Market 4: Base TVL
        bytes32 marketId4 = keccak256("base-tvl-10b");
        TruthyMarket market4 = factory.createMarket(
            marketId4,
            "Will Base TVL exceed $10B by end of Q1 2025?",
            "Total Value Locked on Base network prediction",
            "defi",
            "https://twitter.com/demo/base-tvl",
            deployer,
            block.timestamp + 120 days,
            [0.45e18, 0.55e18],
            750e6
        );
        console.log("Market 4 created at:", address(market4));

        // Demo Market 5: Social - Farcaster
        bytes32 marketId5 = keccak256("farcaster-1m-users");
        TruthyMarket market5 = factory.createMarket(
            marketId5,
            "Will Farcaster reach 1M daily active users in 2024?",
            "Farcaster growth prediction market",
            "social",
            "https://warpcast.com/demo/cast",
            deployer,
            block.timestamp + 60 days,
            [0.35e18, 0.65e18],
            500e6
        );
        console.log("Market 5 created at:", address(market5));

        vm.stopBroadcast();

        console.log("\n=== Demo Markets Created ===");
        console.log("Total markets:", factory.getTotalMarkets());
        console.log("Factory address:", address(factory));
        console.log("USDC address:", address(usdc));
    }
}
