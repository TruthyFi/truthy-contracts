// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.20;

import {Ownable} from "@openzeppelin/contracts/access/Ownable.sol";
import {IERC20} from "@openzeppelin/contracts/token/ERC20/IERC20.sol";
import {SafeERC20} from "@openzeppelin/contracts/token/ERC20/utils/SafeERC20.sol";
import {TruthyMarket} from "./TruthyMarket.sol";

contract TruthyMarketFactory is Ownable {
    using SafeERC20 for IERC20;

    // Payment token (USDC)
    IERC20 public immutable paymentToken;

    // Market creation fee (in payment token, e.g., 5 USDC = 5e6)
    uint256 public creationFee;

    // Accumulated fees
    uint256 public accumulatedFees;

    // Protocol fee rate (in basis points, e.g., 200 = 2%)
    uint256 public protocolFeeRate;

    // Market registry
    mapping(bytes32 => address) private _markets;
    address[] private _allMarkets;

    // Social features
    mapping(address => bytes32[]) private _marketsByCreator;
    mapping(string => bytes32[]) private _marketsByCategory;

    event MarketCreated(
        bytes32 indexed id,
        address indexed creator,
        address indexed marketAddress,
        string name,
        string category,
        string sourceUrl,
        uint256 expiresAt
    );

    event CreationFeeUpdated(uint256 oldFee, uint256 newFee);
    event ProtocolFeeRateUpdated(uint256 oldRate, uint256 newRate);
    event FeesWithdrawn(address indexed to, uint256 amount);

    constructor(address _paymentToken, uint256 _creationFee, uint256 _protocolFeeRate) Ownable(_msgSender()) {
        require(_paymentToken != address(0), "Invalid payment token");
        require(_protocolFeeRate <= 1000, "Fee rate too high"); // Max 10%

        paymentToken = IERC20(_paymentToken);
        creationFee = _creationFee;
        protocolFeeRate = _protocolFeeRate;
    }

    function marketExists(bytes32 id) external view returns (bool) {
        return _markets[id] != address(0);
    }

    function getMarket(bytes32 id) external view returns (address) {
        return _markets[id];
    }

    function getAllMarkets() external view returns (address[] memory) {
        return _allMarkets;
    }

    function getMarketsByCreator(address creator) external view returns (bytes32[] memory) {
        return _marketsByCreator[creator];
    }

    function getMarketsByCategory(string calldata category) external view returns (bytes32[] memory) {
        return _marketsByCategory[category];
    }

    function getTotalMarkets() external view returns (uint256) {
        return _allMarkets.length;
    }

    /// @notice Create a new prediction market (permissionless)
    /// @param id Unique identifier for the market
    /// @param name Market name/question
    /// @param description Detailed description
    /// @param category Category (e.g., "politics", "sports", "crypto")
    /// @param sourceUrl Link to social post or source
    /// @param resolver Address that can resolve the market
    /// @param expiresAt Timestamp when market expires and can be resolved
    /// @param initialPrices Initial prices for [YES, NO] outcomes (must sum to 1e18)
    /// @param initialLiquidity Initial liquidity in payment tokens
    function createMarket(
        bytes32 id,
        string calldata name,
        string calldata description,
        string calldata category,
        string calldata sourceUrl,
        address resolver,
        uint256 expiresAt,
        uint256[2] calldata initialPrices,
        uint256 initialLiquidity
    ) external returns (TruthyMarket market) {
        require(_markets[id] == address(0), "Market already exists");
        require(expiresAt > block.timestamp, "Expiry must be in future");
        require(bytes(name).length > 0, "Name cannot be empty");
        require(resolver != address(0), "Invalid resolver");

        // Collect creation fee
        if (creationFee > 0) {
            paymentToken.safeTransferFrom(msg.sender, address(this), creationFee);
            accumulatedFees += creationFee;
        }

        // Deploy new market
        market = new TruthyMarket(
            address(paymentToken),
            protocolFeeRate,
            msg.sender,  // creator
            resolver,
            id,
            name,
            description,
            category,
            sourceUrl,
            expiresAt,
            initialPrices,
            initialLiquidity
        );

        // Register market
        _markets[id] = address(market);
        _allMarkets.push(address(market));
        _marketsByCreator[msg.sender].push(id);
        _marketsByCategory[category].push(id);

        // Transfer initial liquidity from creator to market
        if (initialLiquidity > 0) {
            paymentToken.safeTransferFrom(msg.sender, address(market), initialLiquidity);
        }

        emit MarketCreated(id, msg.sender, address(market), name, category, sourceUrl, expiresAt);
    }

    /// @notice Update creation fee (only owner)
    function setCreationFee(uint256 newFee) external onlyOwner {
        uint256 oldFee = creationFee;
        creationFee = newFee;
        emit CreationFeeUpdated(oldFee, newFee);
    }

    /// @notice Update protocol fee rate (only owner)
    function setProtocolFeeRate(uint256 newRate) external onlyOwner {
        require(newRate <= 1000, "Fee rate too high"); // Max 10%
        uint256 oldRate = protocolFeeRate;
        protocolFeeRate = newRate;
        emit ProtocolFeeRateUpdated(oldRate, newRate);
    }

    /// @notice Withdraw accumulated fees (only owner)
    function withdrawFees(address to) external onlyOwner {
        require(to != address(0), "Invalid address");
        uint256 amount = accumulatedFees;
        require(amount > 0, "No fees to withdraw");

        accumulatedFees = 0;
        paymentToken.safeTransfer(to, amount);

        emit FeesWithdrawn(to, amount);
    }
}
