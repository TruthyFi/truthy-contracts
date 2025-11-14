// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.20;

import {Ownable} from "@openzeppelin/contracts/access/Ownable.sol";
import {Pausable} from "@openzeppelin/contracts/utils/Pausable.sol";
import {ReentrancyGuard} from "@openzeppelin/contracts/utils/ReentrancyGuard.sol";
import {IERC20} from "@openzeppelin/contracts/token/ERC20/IERC20.sol";
import {SafeERC20} from "@openzeppelin/contracts/token/ERC20/utils/SafeERC20.sol";
import {Math} from "@openzeppelin/contracts/utils/math/Math.sol";

import {OutcomeToken} from "./OutcomeToken.sol";
import {IOutcomeToken} from "./interfaces/IOutcomeToken.sol";
import {IBinaryOutcomeMarket} from "./interfaces/IBinaryOutcome.sol";
import {PricingLibrary} from "./libraries/PricingLibrary.sol";
import {Constants} from "./libraries/Constants.sol";
import {Errors} from "./libraries/Errors.sol";

/// @title TruthyMarket V2 - Refactored
/// @notice Binary prediction market with improved modularity
/// @dev Uses libraries for pricing, constants, and errors (DRY principles)
contract TruthyMarketV2 is IBinaryOutcomeMarket, Ownable, Pausable, ReentrancyGuard {
    using SafeERC20 for IERC20;
    using Math for uint256;

    // ============ Immutable State ============

    IERC20 public immutable paymentToken;
    uint256 public immutable protocolFeeRate;

    // ============ Mutable State ============

    uint256 public accumulatedFees;
    bytes32 private _id;
    string private _name;
    string private _description;
    OutcomeToken[Constants.NUM_OUTCOMES] private _outcomes;
    address private _resolver;
    address private _creator;
    bool private _isResolved;
    bool private _resolvedTo;

    // Social metadata
    string private _category;
    string private _sourceUrl;
    uint256 private _createdAt;
    uint256 private _expiresAt;

    // Trading constraints
    uint256 public minBet;
    uint256 public maxBet;

    // Volume tracking
    uint256 public totalVolume;
    mapping(address => uint256) public userVolume;

    // ============ Events ============

    event OutcomePurchased(
        address indexed buyer, uint256 indexed outcomeIdx, uint256 amount, uint256 cost, uint256 fee
    );
    event OutcomeRedeemed(
        address indexed seller, uint256 indexed outcomeIdx, uint256 amount, uint256 proceeds, uint256 fee
    );
    event MarketResolved(uint256 indexed winningOutcome, uint256 timestamp);
    event FeesWithdrawn(address indexed to, uint256 amount);
    event BetLimitsUpdated(uint256 minBet, uint256 maxBet);
    event LiquidityUpdated(uint256[Constants.NUM_OUTCOMES] newBalances);

    // ============ Modifiers ============

    modifier onlyResolver() {
        if (_msgSender() != _resolver) revert Errors.OnlyResolver();
        _;
    }

    modifier notResolved() {
        if (_isResolved) revert Errors.MarketResolved();
        _;
    }

    modifier canResolve() {
        if (_isResolved) revert Errors.AlreadyResolved();
        if (block.timestamp < _expiresAt) revert Errors.MarketNotExpired();
        _;
    }

    modifier validIndex(uint256 idx) {
        if (idx >= Constants.NUM_OUTCOMES) revert Errors.InvalidIndex();
        _;
    }

    modifier validBetAmount(uint256 amount) {
        if (amount < minBet) revert Errors.BelowMinBet();
        if (amount > maxBet) revert Errors.AboveMaxBet();
        _;
    }

    // ============ Constructor ============

    constructor(
        address _paymentToken,
        uint256 _protocolFeeRate,
        address _marketCreator,
        address __resolver,
        bytes32 __id,
        string memory __name,
        string memory __description,
        string memory __category,
        string memory __sourceUrl,
        uint256 __expiresAt,
        uint256[Constants.NUM_OUTCOMES] memory __initialPrices,
        uint256 __initialLiquidity
    ) Ownable(_marketCreator) {
        // Validation
        if (_paymentToken == address(0)) revert Errors.InvalidPaymentToken();
        if (__resolver == address(0)) revert Errors.InvalidResolver();
        if (__expiresAt <= block.timestamp) revert Errors.ExpiryInPast();
        if (bytes(__name).length == 0) revert Errors.EmptyMarketName();

        _validateInitialPrices(__initialPrices);

        // Set immutables
        paymentToken = IERC20(_paymentToken);
        protocolFeeRate = _protocolFeeRate;

        // Set state
        _creator = _marketCreator;
        _id = __id;
        _name = __name;
        _description = __description;
        _category = __category;
        _sourceUrl = __sourceUrl;
        _resolver = __resolver;
        _createdAt = block.timestamp;
        _expiresAt = __expiresAt;

        // Set default bet limits
        minBet = Constants.DEFAULT_MIN_BET;
        maxBet = Constants.DEFAULT_MAX_BET;

        // Create outcome tokens
        _outcomes[Constants.YES_INDEX] = new OutcomeToken(string(abi.encodePacked(_name, " YES")), "YES");
        _outcomes[Constants.NO_INDEX] = new OutcomeToken(string(abi.encodePacked(_name, " NO")), "NO");

        // Mint initial liquidity
        if (__initialLiquidity > 0) {
            _mintInitialLiquidity(__initialPrices, __initialLiquidity);
        }
    }

    // ============ View Functions ============

    function id() external view returns (bytes32) {
        return _id;
    }

    function name() external view returns (string memory) {
        return _name;
    }

    function description() external view returns (string memory) {
        return _description;
    }

    function category() external view returns (string memory) {
        return _category;
    }

    function sourceUrl() external view returns (string memory) {
        return _sourceUrl;
    }

    function creator() external view returns (address) {
        return _creator;
    }

    function createdAt() external view returns (uint256) {
        return _createdAt;
    }

    function expiresAt() external view returns (uint256) {
        return _expiresAt;
    }

    function isResolved() external view returns (bool) {
        return _isResolved;
    }

    function getResolver() external view returns (address) {
        return _resolver;
    }

    function canResolveNow() external view returns (bool) {
        return !_isResolved && block.timestamp >= _expiresAt;
    }

    function getOutcomeToken(uint256 idx) external view validIndex(idx) returns (IOutcomeToken) {
        return _outcomes[idx];
    }

    function getOutcomePrice(uint256 idx) external view validIndex(idx) returns (uint256) {
        if (_isResolved) {
            return _resolvedTo == (idx == Constants.YES_INDEX) ? Constants.PRECISION : 0;
        }

        uint256[Constants.NUM_OUTCOMES] memory supplies = _getTotalSupplies();
        return PricingLibrary.calculatePrice(supplies[idx], supplies[0] + supplies[1]);
    }

    function getOutcomeLiquidity(uint256 idx) external view validIndex(idx) returns (uint256) {
        return _outcomes[idx].totalSupply();
    }

    function getTotalLiquidity() external view returns (uint256) {
        return _outcomes[Constants.YES_INDEX].totalSupply() + _outcomes[Constants.NO_INDEX].totalSupply();
    }

    function previewCostToBuy(uint256 idx, uint256 amount) external view validIndex(idx) returns (uint256) {
        uint256[Constants.NUM_OUTCOMES] memory supplies = _getTotalSupplies();
        return PricingLibrary.calculateMintCost(supplies[idx], supplies[0] + supplies[1], amount);
    }

    function previewProceedsFromSell(uint256 idx, uint256 amount) external view validIndex(idx) returns (uint256) {
        uint256[Constants.NUM_OUTCOMES] memory supplies = _getTotalSupplies();
        return PricingLibrary.calculateBurnProceeds(supplies[idx], supplies[0] + supplies[1], amount);
    }

    // ============ Trading Functions ============

    function buyOutcome(uint256 idx, uint256 amount)
        external
        whenNotPaused
        nonReentrant
        notResolved
        validIndex(idx)
        validBetAmount(amount)
        returns (uint256 cost, uint256 fee)
    {
        address sender = _msgSender();

        // Calculate cost and fee
        uint256[Constants.NUM_OUTCOMES] memory supplies = _getTotalSupplies();
        uint256 baseCost = PricingLibrary.calculateMintCost(supplies[idx], supplies[0] + supplies[1], amount);
        fee = baseCost.mulDiv(protocolFeeRate, Constants.FEE_PRECISION);
        cost = baseCost + fee;

        // Transfer payment
        paymentToken.safeTransferFrom(sender, address(this), cost);

        // Mint outcome tokens
        _outcomes[idx].mint(sender, amount);

        // Update state
        accumulatedFees += fee;
        totalVolume += baseCost;
        userVolume[sender] += baseCost;

        emit OutcomePurchased(sender, idx, amount, cost, fee);
    }

    function redeemOutcome(uint256 idx, uint256 amount)
        external
        whenNotPaused
        nonReentrant
        validIndex(idx)
        returns (uint256 proceeds, uint256 fee)
    {
        address sender = _msgSender();

        if (_outcomes[idx].balanceOf(sender) < amount) revert Errors.InsufficientBalance();

        // Calculate proceeds
        if (_isResolved) {
            (proceeds, fee) = _calculateResolvedProceeds(idx, amount);
        } else {
            (proceeds, fee) = _calculateUnresolvedProceeds(idx, amount);
        }

        // Burn tokens
        _outcomes[idx].burn(sender, amount);

        // Transfer proceeds
        if (proceeds > 0) {
            paymentToken.safeTransfer(sender, proceeds);
        }

        emit OutcomeRedeemed(sender, idx, amount, proceeds, fee);
    }

    // ============ Resolution Functions ============

    function resolve(uint256 idx) external onlyResolver canResolve validIndex(idx) {
        _isResolved = true;
        _resolvedTo = idx == Constants.YES_INDEX;

        // Burn contract-held liquidity
        uint256[Constants.NUM_OUTCOMES] memory balances = _getOutcomeBalances();
        for (uint256 i = 0; i < Constants.NUM_OUTCOMES; ++i) {
            if (balances[i] > 0) {
                _outcomes[i].burn(address(this), balances[i]);
            }
        }

        emit MarketResolved(idx, block.timestamp);
    }

    // ============ Admin Functions ============

    function updateLiquidityBalances(uint256[Constants.NUM_OUTCOMES] memory newBalances)
        external
        onlyOwner
        notResolved
    {
        uint256[Constants.NUM_OUTCOMES] memory currentBalances = _getOutcomeBalances();

        for (uint256 i = 0; i < Constants.NUM_OUTCOMES; ++i) {
            if (newBalances[i] > currentBalances[i]) {
                _outcomes[i].mint(address(this), newBalances[i] - currentBalances[i]);
            } else if (newBalances[i] < currentBalances[i]) {
                _outcomes[i].burn(address(this), currentBalances[i] - newBalances[i]);
            }
        }

        emit LiquidityUpdated(newBalances);
    }

    function pause() external onlyOwner {
        _pause();
    }

    function unpause() external onlyOwner {
        _unpause();
    }

    function setBetLimits(uint256 _minBet, uint256 _maxBet) external onlyOwner {
        if (_minBet >= _maxBet) revert Errors.MinBetGreaterThanMax();
        if (_minBet == 0) revert Errors.MinBetMustBePositive();

        minBet = _minBet;
        maxBet = _maxBet;

        emit BetLimitsUpdated(_minBet, _maxBet);
    }

    function withdrawFees(address to) external onlyOwner {
        if (to == address(0)) revert Errors.InvalidAddress();

        uint256 amount = accumulatedFees;
        if (amount == 0) revert Errors.NoFeesToWithdraw();

        accumulatedFees = 0;
        paymentToken.safeTransfer(to, amount);

        emit FeesWithdrawn(to, amount);
    }

    // ============ Internal Functions ============

    function _validateInitialPrices(uint256[Constants.NUM_OUTCOMES] memory prices) private pure {
        if (prices[0] >= Constants.PRECISION || prices[1] >= Constants.PRECISION) {
            revert Errors.InvalidPrice();
        }
        if (prices[0] + prices[1] != Constants.PRECISION) {
            revert Errors.InvalidPriceSum();
        }
    }

    function _mintInitialLiquidity(uint256[Constants.NUM_OUTCOMES] memory prices, uint256 liquidity) private {
        for (uint256 i = 0; i < Constants.NUM_OUTCOMES; ++i) {
            uint256 amount = liquidity.mulDiv(prices[i], Constants.PRECISION);
            _outcomes[i].mint(address(this), amount);
        }
    }

    function _calculateResolvedProceeds(uint256 idx, uint256 amount)
        private
        view
        returns (uint256 proceeds, uint256 fee)
    {
        if (_resolvedTo == (idx == Constants.YES_INDEX)) {
            proceeds = amount; // 1:1 redemption
            fee = 0; // No fee on winning redemption
        } else {
            proceeds = 0; // Losing tokens are worthless
            fee = 0;
        }
    }

    function _calculateUnresolvedProceeds(uint256 idx, uint256 amount)
        private
        returns (uint256 proceeds, uint256 fee)
    {
        uint256[Constants.NUM_OUTCOMES] memory supplies = _getTotalSupplies();
        uint256 baseProceeds = PricingLibrary.calculateBurnProceeds(supplies[idx], supplies[0] + supplies[1], amount);

        fee = baseProceeds.mulDiv(protocolFeeRate, Constants.FEE_PRECISION);
        proceeds = baseProceeds - fee;

        // Update state
        accumulatedFees += fee;
        totalVolume += baseProceeds;
        userVolume[_msgSender()] += baseProceeds;
    }

    function _getTotalSupplies() private view returns (uint256[Constants.NUM_OUTCOMES] memory supplies) {
        for (uint256 i = 0; i < Constants.NUM_OUTCOMES; ++i) {
            supplies[i] = _outcomes[i].totalSupply();
        }
    }

    function _getOutcomeBalances() private view returns (uint256[Constants.NUM_OUTCOMES] memory balances) {
        for (uint256 i = 0; i < Constants.NUM_OUTCOMES; ++i) {
            balances[i] = _outcomes[i].balanceOf(address(this));
        }
    }
}
