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

contract TruthyMarket is IBinaryOutcomeMarket, Ownable, Pausable, ReentrancyGuard {
    using SafeERC20 for IERC20;
    using Math for uint256;

    uint256 private constant PRECISION = 1e18;
    uint256 private constant FEE_PRECISION = 10000; // Basis points (100 = 1%)

    // Payment token (USDC)
    IERC20 public immutable paymentToken;

    // Protocol fee rate (basis points)
    uint256 public immutable protocolFeeRate;

    // Accumulated protocol fees
    uint256 public accumulatedFees;

    // Core market data
    bytes32 private _id;
    string private _name;
    string private _description;
    OutcomeToken[2] private _outcomes;
    address private _resolver;
    address private _creator;
    bool private _isResolved;
    bool private _resolvedTo;

    // Social metadata
    string private _category;
    string private _sourceUrl;
    uint256 private _createdAt;
    uint256 private _expiresAt;

    // Bet limits (in payment token units, e.g., USDC has 6 decimals)
    uint256 public minBet;
    uint256 public maxBet;

    // Trading volume tracking
    uint256 public totalVolume;
    mapping(address => uint256) public userVolume;

    event OutcomePurchased(address indexed buyer, uint256 indexed outcomeIdx, uint256 amount, uint256 cost, uint256 fee);
    event OutcomeRedeemed(address indexed seller, uint256 indexed outcomeIdx, uint256 amount, uint256 proceeds, uint256 fee);
    event MarketResolved(uint256 indexed winningOutcome, uint256 timestamp);
    event FeesWithdrawn(address indexed to, uint256 amount);
    event BetLimitsUpdated(uint256 minBet, uint256 maxBet);

    modifier onlyResolver() {
        require(_msgSender() == _resolver, "Only resolver");
        _;
    }

    modifier notResolved() {
        require(!_isResolved, "Market resolved");
        _;
    }

    modifier canResolve() {
        require(!_isResolved, "Already resolved");
        require(block.timestamp >= _expiresAt, "Market not expired");
        _;
    }

    modifier validIndex(uint256 idx) {
        require(idx < 2, "Invalid index");
        _;
    }

    modifier validBetAmount(uint256 amount) {
        require(amount >= minBet, "Below min bet");
        require(amount <= maxBet, "Above max bet");
        _;
    }

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
        uint256[2] memory __initialPrices,
        uint256 __initialLiquidity
    ) Ownable(_marketCreator) {
        require(_paymentToken != address(0), "Invalid payment token");
        require(__initialPrices[0] < PRECISION && __initialPrices[1] < PRECISION, "Prices must be < 1.0");
        require(__initialPrices[0] + __initialPrices[1] == PRECISION, "Prices must sum to 1.0");
        require(__expiresAt > block.timestamp, "Expiry in past");
        require(__resolver != address(0), "Invalid resolver");

        paymentToken = IERC20(_paymentToken);
        protocolFeeRate = _protocolFeeRate;
        _creator = _marketCreator;
        _id = __id;
        _name = __name;
        _description = __description;
        _category = __category;
        _sourceUrl = __sourceUrl;
        _resolver = __resolver;
        _createdAt = block.timestamp;
        _expiresAt = __expiresAt;

        // Default bet limits (can be updated by owner)
        // Assuming 6 decimals for USDC
        minBet = 0.5e6;    // $0.50 minimum
        maxBet = 1000e6;   // $1000 maximum

        // Create outcome tokens
        _outcomes[0] = new OutcomeToken(string(abi.encodePacked(_name, " YES")), "YES");
        _outcomes[1] = new OutcomeToken(string(abi.encodePacked(_name, " NO")), "NO");

        // Mint initial liquidity if provided
        if (__initialLiquidity > 0) {
            _outcomes[0].mint(address(this), __initialLiquidity.mulDiv(__initialPrices[0], PRECISION));
            _outcomes[1].mint(address(this), __initialLiquidity.mulDiv(__initialPrices[1], PRECISION));
        }
    }

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
        // TODO: Make sure 1:1 is the correct exchange rate after resolution
        if (_isResolved) return _resolvedTo == (idx == 0) ? 1e18 : 0;
        return _getOutcomePrice(idx, _getTotalSupplies());
    }

    function getOutcomeLiquidity(uint256 idx) external view validIndex(idx) returns (uint256) {
        return _outcomes[idx].totalSupply();
    }

    function getTotalLiquidity() external view returns (uint256) {
        return _outcomes[0].totalSupply() + _outcomes[1].totalSupply();
    }

    function previewCostToBuy(uint256 idx, uint256 amount) external view validIndex(idx) returns (uint256) {
        return _getCostToMint(idx, amount, _getTotalSupplies());
    }

    function previewProceedsFromSell(uint256 idx, uint256 amount) external view validIndex(idx) returns (uint256) {
        return _getProceedsFromBurn(idx, amount, _getTotalSupplies());
    }

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

        // Calculate cost before fees
        uint256 baseCost = _getCostToMint(idx, amount, _getTotalSupplies());

        // Calculate protocol fee
        fee = baseCost.mulDiv(protocolFeeRate, FEE_PRECISION);
        cost = baseCost + fee;

        // Transfer payment from user
        paymentToken.safeTransferFrom(sender, address(this), cost);

        // Mint outcome tokens to user
        _outcomes[idx].mint(sender, amount);

        // Track fees and volume
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
        require(_outcomes[idx].balanceOf(sender) >= amount, "Insufficient balance");

        uint256 baseProceeds;

        if (_isResolved) {
            if (_resolvedTo == (idx == 0)) {
                // Redeem winning outcome 1:1 for payment token
                baseProceeds = amount;
                fee = 0; // No fee on redemption of winning outcomes
            } else {
                // Losing outcome is worthless
                baseProceeds = 0;
                fee = 0;
            }
        } else {
            // Selling before resolution
            baseProceeds = _getProceedsFromBurn(idx, amount, _getTotalSupplies());

            // Calculate protocol fee
            fee = baseProceeds.mulDiv(protocolFeeRate, FEE_PRECISION);
            baseProceeds -= fee;

            // Track fees and volume
            accumulatedFees += fee;
            totalVolume += baseProceeds;
            userVolume[sender] += baseProceeds;
        }

        proceeds = baseProceeds;

        // Burn outcome tokens
        _outcomes[idx].burn(sender, amount);

        // Transfer proceeds to user
        if (proceeds > 0) {
            paymentToken.safeTransfer(sender, proceeds);
        }

        emit OutcomeRedeemed(sender, idx, amount, proceeds, fee);
    }

    function resolve(uint256 idx) external onlyResolver canResolve validIndex(idx) {
        // Store resolution status
        _isResolved = true;
        _resolvedTo = idx == 0;

        // Burn the liquidity outcome tokens held by this contract
        // After this, remaining tokens are held by users & winning outcome can be redeemed
        uint256[2] memory balancesThis = _getOutcomeBalances();
        for (uint256 i; i < 2; ++i) {
            if (balancesThis[i] > 0) {
                _outcomes[i].burn(address(this), balancesThis[i]);
            }
        }

        emit MarketResolved(idx, block.timestamp);
    }

    /// @notice Update the outcome token balances of this contract to match external market prices
    /// @dev Only callable by owner before resolution
    /// @param newBalances The new balances of the outcome tokens
    function updateLiquidityBalances(uint256[2] memory newBalances) external onlyOwner notResolved {
        uint256[2] memory balancesThis = _getOutcomeBalances();
        for (uint256 i; i < 2; ++i) {
            if (newBalances[i] > balancesThis[i]) {
                _outcomes[i].mint(address(this), newBalances[i] - balancesThis[i]);
            } else if (newBalances[i] < balancesThis[i]) {
                _outcomes[i].burn(address(this), balancesThis[i] - newBalances[i]);
            }
        }
    }

    /// @notice Pause trading (emergency only)
    function pause() external onlyOwner {
        _pause();
    }

    /// @notice Unpause trading
    function unpause() external onlyOwner {
        _unpause();
    }

    /// @notice Update bet limits
    function setBetLimits(uint256 _minBet, uint256 _maxBet) external onlyOwner {
        require(_minBet < _maxBet, "Min must be < max");
        require(_minBet > 0, "Min must be > 0");
        minBet = _minBet;
        maxBet = _maxBet;
        emit BetLimitsUpdated(_minBet, _maxBet);
    }

    /// @notice Withdraw accumulated protocol fees (only owner)
    function withdrawFees(address to) external onlyOwner {
        require(to != address(0), "Invalid address");
        uint256 amount = accumulatedFees;
        require(amount > 0, "No fees to withdraw");

        accumulatedFees = 0;
        paymentToken.safeTransfer(to, amount);

        emit FeesWithdrawn(to, amount);
    }

    function _getOutcomePrice(uint256 idx, uint256[2] memory outcomeTotals) private pure returns (uint256) {
        return outcomeTotals[idx].mulDiv(PRECISION, outcomeTotals[0] + outcomeTotals[1]);
    }

    function _getOutcomePriceAfterMint(uint256 idx, uint256 amount, uint256[2] memory outcomeTotals)
        private
        pure
        returns (uint256)
    {
        return (outcomeTotals[idx] + amount).mulDiv(PRECISION, outcomeTotals[0] + outcomeTotals[1] + amount);
    }

    function _getOutcomePriceAfterBurn(uint256 idx, uint256 amount, uint256[2] memory outcomeTotals)
        private
        pure
        returns (uint256)
    {
        return (outcomeTotals[idx] - amount).mulDiv(PRECISION, outcomeTotals[0] + outcomeTotals[1] - amount);
    }

    function _getAveragePriceToMint(uint256 idx, uint256 amount, uint256[2] memory outcomeTotals)
        private
        pure
        returns (uint256)
    {
        return Math.average(_getOutcomePrice(idx, outcomeTotals), _getOutcomePriceAfterMint(idx, amount, outcomeTotals));
    }

    function _getAveragePriceToBurn(uint256 idx, uint256 amount, uint256[2] memory outcomeTotals)
        private
        pure
        returns (uint256)
    {
        return Math.average(_getOutcomePrice(idx, outcomeTotals), _getOutcomePriceAfterBurn(idx, amount, outcomeTotals));
    }

    function _getCostToMint(uint256 idx, uint256 amount, uint256[2] memory outcomeTotals)
        private
        pure
        returns (uint256)
    {
        return amount.mulDiv(_getAveragePriceToMint(idx, amount, outcomeTotals), PRECISION);
    }

    function _getProceedsFromBurn(uint256 idx, uint256 amount, uint256[2] memory outcomeTotals)
        private
        pure
        returns (uint256)
    {
        return amount.mulDiv(_getAveragePriceToBurn(idx, amount, outcomeTotals), PRECISION);
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
