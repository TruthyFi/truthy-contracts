// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.20;

import {Script, console} from "forge-std/Script.sol";
import {TruthyMarketFactory} from "../src/TruthyMarketFactory.sol";
import {TruthyMarket} from "../src/TruthyMarket.sol";
import {MockUSDC} from "../src/mocks/MockUSDC.sol";

contract DeployScript is Script {
    // Configuration
    uint256 public constant CREATION_FEE = 5e6; // 5 USDC to create a market
    uint256 public constant PROTOCOL_FEE_RATE = 200; // 2% (200 basis points)

    function run() external {
        uint256 deployerPrivateKey = vm.envUint("PRIVATE_KEY");
        address deployer = vm.addr(deployerPrivateKey);

        console.log("Deploying from:", deployer);
        console.log("Chain ID:", block.chainid);

        vm.startBroadcast(deployerPrivateKey);

        // Deploy Mock USDC for testnet (use real USDC on mainnet)
        MockUSDC usdc;
        if (block.chainid == 84532) {
            // Base Sepolia - deploy mock
            usdc = new MockUSDC();
            console.log("MockUSDC deployed at:", address(usdc));
        } else if (block.chainid == 8453) {
            // Base Mainnet - use real USDC
            usdc = MockUSDC(0x833589fCD6eDb6E08f4c7C32D4f71b54bdA02913);
            console.log("Using real USDC at:", address(usdc));
        } else {
            // Local/other - deploy mock
            usdc = new MockUSDC();
            console.log("MockUSDC deployed at:", address(usdc));
        }

        // Deploy Factory
        TruthyMarketFactory factory = new TruthyMarketFactory(
            address(usdc),
            CREATION_FEE,
            PROTOCOL_FEE_RATE
        );

        console.log("TruthyMarketFactory deployed at:", address(factory));
        console.log("Payment token:", address(usdc));
        console.log("Creation fee:", CREATION_FEE);
        console.log("Protocol fee rate:", PROTOCOL_FEE_RATE);

        vm.stopBroadcast();

        // Write deployment addresses to file
        string memory json = string(
            abi.encodePacked(
                '{\n',
                '  "chainId": ', vm.toString(block.chainid), ',\n',
                '  "factory": "', vm.toString(address(factory)), '",\n',
                '  "usdc": "', vm.toString(address(usdc)), '",\n',
                '  "creationFee": ', vm.toString(CREATION_FEE), ',\n',
                '  "protocolFeeRate": ', vm.toString(PROTOCOL_FEE_RATE), '\n',
                '}'
            )
        );

        string memory fileName = string(
            abi.encodePacked("deployments/", vm.toString(block.chainid), ".json")
        );

        vm.writeFile(fileName, json);
        console.log("Deployment info written to:", fileName);
    }
}
