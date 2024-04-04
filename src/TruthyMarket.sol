// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.20;

import {Context} from "@openzeppelin/contracts/utils/Context.sol";
import {Ownable} from "@openzeppelin/contracts/access/Ownable.sol";
import {UD60x18, ud} from "prb-math/src/UD60x18.sol";
import {OutcomeToken} from "./OutcomeToken.sol";
import {IOutcomeToken} from "./interfaces/IOutcomeToken.sol";
import {IBinaryOutcomeMarket} from "./interfaces/IBinaryOutcome.sol";

contract TruthyMarket is IBinaryOutcomeMarket, Ownable {
    string private _id;
    string private _name;
    string private _description;
    OutcomeToken[2] private _outcomes;
    address private _resolver;
    bool private _isResolved;

    constructor(
        address __owner,
        address __resolver,
        string memory __id,
        string memory __name,
        string memory __description,
        uint256[2] memory __initialPrices,
        uint256 __initialLiquidity
    ) Ownable(__owner) {
        require(__initialPrices[0] < 1e18 && __initialPrices[1] < 1e18, "Prices must be less than 1.0");
        require(__initialPrices[0] + __initialPrices[1] == 1e18, "Prices must sum to 1.0");
        _id = __id;
        _name = __name;
        _description = __description;
        _resolver = __resolver;
        _outcomes[0] = new OutcomeToken(string(abi.encodePacked(_name, " YES")), "YES");
        _outcomes[1] = new OutcomeToken(string(abi.encodePacked(_name, " NO")), "NO");
        // Mint initial liquidity based on Polymarket:
        UD60x18 initialLiquidity = ud(__initialLiquidity);
        _outcomes[0].mint(address(this), initialLiquidity.mul(ud(__initialPrices[0])).intoUint256());
        _outcomes[1].mint(address(this), initialLiquidity.mul(ud(__initialPrices[1])).intoUint256());
    }

    function id() external view returns (string memory) {
        return _id;
    }

    function name() external view returns (string memory) {
        return _name;
    }

    function description() external view returns (string memory) {
        return _description;
    }

    function isResolved() external view returns (bool) {
        return _isResolved;
    }

    function getResolver() external view returns (address) {
        return _resolver;
    }

    function getOutcomeToken(uint256 idx) external view returns (IOutcomeToken) {
        return _outcomes[idx];
    }

    function getOutcomePrice(uint256 idx) external view returns (uint256) {
        UD60x18[2] memory outcomeTotals = _getTotalSupplies();
        return outcomeTotals[idx].div(outcomeTotals[0] + outcomeTotals[1]).intoUint256();
    }

    function getOutcomeLiquidity(uint256 idx) external view returns (uint256) {
        return _outcomes[idx].totalSupply();
    }

    function getTotalLiquidity() external view returns (uint256) {
        return _outcomes[0].totalSupply() + _outcomes[1].totalSupply();
    }

    function buyOutcome(uint256 idx) external payable {}

    function redeemOutcome(uint256 idx, uint256 amount) external {}

    function resolve(uint256 idx) external {}

    function _getTotalSupplies() private view returns (UD60x18[2] memory supplies) {
        supplies[0] = ud(_outcomes[0].totalSupply());
        supplies[1] = ud(_outcomes[1].totalSupply());
    }
}
