// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.20;

import {IOutcomeToken} from "./IOutcomeToken.sol";

interface IBinaryOutcomeMarket {
    function id() external view returns (string memory);

    function name() external view returns (string memory);

    function description() external view returns (string memory);

    function isResolved() external view returns (bool);

    function getResolver() external view returns (address);

    function getOutcomeToken(uint256 idx) external view returns (IOutcomeToken);

    function getOutcomePrice(uint256 idx) external view returns (uint256);

    function getOutcomeLiquidity(uint256 idx) external view returns (uint256);

    function getTotalLiquidity() external view returns (uint256);

    function buyOutcome(uint256 idx, uint256 amount) external payable returns (uint256);

    function redeemOutcome(uint256 idx, uint256 amount) external returns (uint256);

    function resolve(uint256 idx) external;
}
