// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.20;

import {Ownable} from "@openzeppelin/contracts/access/Ownable.sol";
import {Address} from "@openzeppelin/contracts/utils/Address.sol";
import {Math} from "@openzeppelin/contracts/utils/math/Math.sol";
import {OutcomeToken} from "./OutcomeToken.sol";
import {IOutcomeToken} from "./interfaces/IOutcomeToken.sol";
import {IBinaryOutcomeMarket} from "./interfaces/IBinaryOutcome.sol";

contract TruthyMarket is IBinaryOutcomeMarket, Ownable {
    using Address for address payable;
    using Math for uint256;

    uint256 private constant PRECISION = 1e18;
    string private _id;
    string private _name;
    string private _description;
    OutcomeToken[2] private _outcomes;
    address private _resolver;
    bool private _isResolved;
    bool private _resolvedTo;

    modifier onlyResolver() {
        require(_msgSender() == _resolver, "Only the resolver can call this function");
        _;
    }

    modifier notResolved() {
        require(!_isResolved, "Market already resolved");
        _;
    }

    modifier validIndex(uint256 idx) {
        require(idx < 2, "Index out of bounds");
        _;
    }

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
        _outcomes[0].mint(address(this), __initialLiquidity.mulDiv(__initialPrices[0], PRECISION));
        _outcomes[1].mint(address(this), __initialLiquidity.mulDiv(__initialPrices[1], PRECISION));
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

    function getOutcomeToken(uint256 idx) external view validIndex(idx) returns (IOutcomeToken) {
        return _outcomes[idx];
    }

    function getOutcomePrice(uint256 idx) external view validIndex(idx) returns (uint256) {
        if (_isResolved) return _resolvedTo == (idx == 0) ? 1e18 : 0;
        uint256[2] memory outcomeTotals = _getTotalSupplies();
        return outcomeTotals[idx].mulDiv(PRECISION, outcomeTotals[0] + outcomeTotals[1]);
    }

    function getOutcomeLiquidity(uint256 idx) external view validIndex(idx) returns (uint256) {
        return _outcomes[idx].totalSupply();
    }

    function getTotalLiquidity() external view returns (uint256) {
        return _outcomes[0].totalSupply() + _outcomes[1].totalSupply();
    }

    function buyOutcome(uint256 idx) external payable notResolved validIndex(idx) {}

    function redeemOutcome(uint256 idx, uint256 amount) external validIndex(idx) {}

    function resolve(uint256 idx) external onlyResolver notResolved validIndex(idx) {
        // Store resolution status
        _isResolved = true;
        _resolvedTo = idx == 0;

        // Burn the "dummy" outcome tokens held by this contract, representing positions on Polymarket
        // After this, remaining tokens are held by users & winning outcome can be redeemed for $DEGEN
        uint256[2] memory balancesThis = _getOutcomeBalances();
        for (uint256 i; i < 2; ++i) {
            _outcomes[i].burn(address(this), balancesThis[i]);
        }
    }

    /// @notice Update the outcome token balances of this contract to match updated prices on Polymarket
    /// @dev inputs should be determined by `newBalance[i] = totalMarketLiquidity * outcomePrice[i]`,
    ///      where `0 < outcomePrice[i] < 1 && outcomePrice[0] + outcomePrice[1] == 1`
    /// @param newBalances The new balances of the outcome tokens
    function updatePolymarketBalances(uint256[2] memory newBalances) external onlyOwner notResolved {
        uint256[2] memory balancesThis = _getOutcomeBalances();
        for (uint256 i; i < 2; ++i) {
            if (newBalances[i] > balancesThis[i]) {
                _outcomes[i].mint(address(this), newBalances[i] - balancesThis[i]);
            } else if (newBalances[i] < balancesThis[i]) {
                _outcomes[i].burn(address(this), balancesThis[i] - newBalances[i]);
            }
        }
    }

    function _getTotalSupplies() private view returns (uint256[2] memory supplies) {
        supplies[0] = _outcomes[0].totalSupply();
        supplies[1] = _outcomes[1].totalSupply();
    }

    function _getOutcomeBalances() private view returns (uint256[2] memory balances) {
        balances[0] = _outcomes[0].balanceOf(address(this));
        balances[1] = _outcomes[1].balanceOf(address(this));
    }
}
