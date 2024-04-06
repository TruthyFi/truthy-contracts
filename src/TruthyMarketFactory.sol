// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.20;

import {Ownable} from "@openzeppelin/contracts/access/Ownable.sol";
import {TruthyMarket} from "./TruthyMarket.sol";

contract TruthyMarketFactory is Ownable {
    mapping(bytes32 => address) private _markets;

    constructor() Ownable(_msgSender()) {}

    function marketExists(bytes32 id) external view returns (bool) {
        return _markets[id] != address(0);
    }

    function getMarket(bytes32 id) external view returns (address) {
        return _markets[id];
    }

    function createMarket(
        address resolver,
        bytes32 id,
        string memory name,
        string memory description,
        uint256[2] memory initialPrices,
        uint256 initialLiquidity
    ) external onlyOwner returns (TruthyMarket market) {
        require(_markets[id] == address(0), "Market already exists");
        market = new TruthyMarket(_msgSender(), resolver, id, name, description, initialPrices, initialLiquidity);
        _markets[id] = address(market);
    }
}
