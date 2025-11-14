# TruthyFi - Social Prediction Markets on Base

> **Put your money where your mouth is** - The first social network powered by prediction markets

TruthyFi combines the engagement of Twitter/Farcaster with the accountability of Polymarket. Every claim, post, or prediction can become a market where users bet with real money, building reputation through accurate predictions.

## 🎯 What Makes TruthyFi Different?

- **🌐 Social-First**: Create markets on any claim, link to social posts, track your credibility on-chain
- **💰 Micro-Bets**: Start with as little as $0.50 - accessible to everyone
- **⚡ Base-Native**: Ultra-low fees (~$0.01/trade) on Base L2
- **🔓 Permissionless**: Anyone can create a market for $5 USDC
- **🎭 Farcaster Integration**: Bet directly from your social feed with Frames
- **📊 Transparent**: All positions and outcomes visible on-chain

## 📋 Table of Contents

- [Quick Start - Local Testing](#-quick-start---local-testing)
- [Architecture](#architecture)
- [Smart Contracts](#smart-contracts)
- [Getting Started](#getting-started)
- [Deployment](#deployment)
- [Testing](#testing)
- [Frontend](#frontend)
- [Grant Applications](#grant-applications)
- [Roadmap](#roadmap)

## ⚡ Quick Start - Local Testing

**Run TruthyFi locally in 5 minutes:**

```bash
# 1. One-command setup (automated)
bash scripts/local-test.sh

# 2. Start frontend (in new terminal)
cd frontend
npm run dev

# 3. Open http://localhost:3000 and connect MetaMask!
```

**What you get:**
- ✅ Local blockchain running (Anvil)
- ✅ All contracts deployed
- ✅ 5 demo markets created
- ✅ Test USDC funded
- ✅ Frontend configured
- ✅ Ready to trade!

**📚 Detailed Guides:**
- [LOCAL_TESTING_GUIDE.md](./LOCAL_TESTING_GUIDE.md) - Complete local testing guide
- [scripts/README.md](./scripts/README.md) - Automation scripts documentation
- [DEPLOYMENT_RUNBOOK.md](./DEPLOYMENT_RUNBOOK.md) - Production deployment

**🎬 Quick Demo:**
```bash
# After setup, run an automated demo
bash scripts/demo.sh
```

This shows a complete trade flow: getting USDC, buying tokens, selling tokens, and viewing results.

## 🏗 Architecture

```
┌─────────────────────┐
│  Farcaster/Social   │  ← Users create/share predictions
└──────────┬──────────┘
           │
           ↓
┌─────────────────────┐
│   Frontend (Web)    │  ← Browse markets, place bets
└──────────┬──────────┘
           │
           ↓
┌─────────────────────┐
│ TruthyMarketFactory │  ← Deploy new markets (permissionless)
└──────────┬──────────┘
           │
           ↓
┌─────────────────────┐
│   TruthyMarket(s)   │  ← Binary prediction markets (YES/NO)
└──────────┬──────────┘
           │
           ↓
┌─────────────────────┐
│  OutcomeTokens (2)  │  ← ERC20 tokens for positions
└─────────────────────┘
           │
           ↓
┌─────────────────────┐
│    USDC (Base)      │  ← Stablecoin payments
└─────────────────────┘
```

## 📜 Smart Contracts

### TruthyMarketFactory

Factory contract for permissionless market creation.

**Key Features:**
- Anyone can create a market (pays $5 USDC fee)
- Tracks markets by creator, category, ID
- Configurable protocol fees (default: 2%)
- Fee collection for protocol sustainability

**Functions:**
```solidity
function createMarket(
    bytes32 id,
    string calldata name,
    string calldata description,
    string calldata category,      // "crypto", "politics", "sports", etc.
    string calldata sourceUrl,     // Link to tweet/post
    address resolver,              // Who can resolve this market
    uint256 expiresAt,            // When market expires
    uint256[2] calldata initialPrices,  // [YES_price, NO_price] in 1e18
    uint256 initialLiquidity      // USDC amount
) external returns (TruthyMarket)
```

### TruthyMarket

Individual binary prediction market (YES/NO outcomes).

**Key Features:**
- USDC-denominated bets (6 decimals)
- Min bet: $0.50, Max bet: $1,000 (configurable)
- Protocol fee: 2% on trades (0% on winning redemptions)
- Pausable for emergencies
- ReentrancyGuard protection
- Automated pricing based on supply

**Trading Functions:**
```solidity
// Buy outcome tokens
function buyOutcome(uint256 idx, uint256 amount) external returns (uint256 cost, uint256 fee)

// Sell outcome tokens or redeem winnings
function redeemOutcome(uint256 idx, uint256 amount) external returns (uint256 proceeds, uint256 fee)

// Resolve market (resolver only, after expiry)
function resolve(uint256 idx) external
```

**Pricing Mechanism:**
- Simple supply-based pricing: `price = supply[i] / totalSupply`
- Average pricing on trades (prevents front-running)
- 1:1 redemption for winning outcomes

### OutcomeToken

ERC20 token representing YES or NO positions.

**Features:**
- Mintable/burnable only by parent market
- Transferable (can trade on secondary markets)
- Standard ERC20 interface

### MockUSDC (Testnet Only)

Mock USDC for testing with faucet function.

## 🚀 Getting Started

### Prerequisites

- [Foundry](https://book.getfoundry.sh/getting-started/installation)
- [Node.js v18+](https://nodejs.org/) (for frontend)
- [Git](https://git-scm.com/)

### Installation

```bash
# Clone the repo
git clone https://github.com/TruthyFi/truthy-contracts.git
cd truthy-contracts

# Install dependencies
forge install

# Copy environment variables
cp .env.example .env
# Edit .env with your private key and API keys
```

### Build

```bash
forge build
```

### Test

```bash
# Run all tests
forge test

# Run with gas report
forge test --gas-report

# Run with coverage
forge coverage

# Run specific test
forge test --match-test testBuyOutcome -vvv
```

## 🌐 Deployment

### Deploy to Base Sepolia (Testnet)

1. **Get testnet ETH:**
   - Get Base Sepolia ETH from [faucet](https://www.coinbase.com/faucets/base-ethereum-goerli-faucet)

2. **Set up environment:**
```bash
# .env file
PRIVATE_KEY=your_private_key_here
BASESCAN_API_KEY=your_basescan_api_key
```

3. **Deploy contracts:**
```bash
forge script script/Deploy.s.sol:DeployScript \
  --rpc-url base_sepolia \
  --broadcast \
  --verify
```

4. **Create demo markets:**
```bash
# Set deployed addresses in .env
FACTORY_ADDRESS=0x...
USDC_ADDRESS=0x...

# Create markets
forge script script/CreateDemoMarket.s.sol:CreateDemoMarketScript \
  --rpc-url base_sepolia \
  --broadcast
```

### Deploy to Base Mainnet

```bash
forge script script/Deploy.s.sol:DeployScript \
  --rpc-url base \
  --broadcast \
  --verify \
  --slow
```

**Note:** On mainnet, the script uses real USDC at `0x833589fCD6eDb6E08f4c7C32D4f71b54bdA02913`

## 🧪 Testing

### Test Coverage

Current test coverage includes:
- ✅ Factory deployment and configuration
- ✅ Permissionless market creation
- ✅ Social metadata tracking
- ✅ Buying/selling outcome tokens
- ✅ Fee collection and withdrawal
- ✅ Market resolution and redemption
- ✅ Pause/unpause functionality
- ✅ Bet limit enforcement
- ✅ Access control

### Gas Benchmarks

| Operation | Gas Cost | USD Cost (Base) |
|-----------|----------|-----------------|
| Create Market | ~500-800k | ~$0.25-0.40 |
| Buy Outcome | ~150-200k | ~$0.08-0.10 |
| Sell Outcome | ~100-150k | ~$0.05-0.08 |
| Resolve Market | ~200-300k | ~$0.10-0.15 |

*Based on 0.5 gwei gas price on Base*

## 🎨 Frontend

### Tech Stack

- **Framework**: Next.js 14 (App Router)
- **Styling**: Tailwind CSS
- **Web3**: wagmi v2 + viem
- **Wallet**: RainbowKit
- **State**: TanStack Query
- **Blockchain**: Base (Sepolia for testnet)

### Setup Frontend (Coming Soon)

```bash
cd frontend
npm install
npm run dev
```

### Features

- 🏪 Market discovery and browsing
- 📝 Create new markets
- 💰 Buy/sell outcome tokens
- 👤 User profiles with betting history
- 📊 Win rate and volume tracking
- 🎯 Category filtering
- 🔍 Search markets
- 📱 Mobile-responsive

## 🎭 Farcaster Integration

### Farcaster Frames

TruthyFi uses Farcaster Frames to enable in-feed betting:

```typescript
// Example Frame
POST /api/frames/market/:id

Response:
{
  "image": "Market preview with current odds",
  "buttons": [
    { "label": "YES ($1)", "action": "tx", "target": "/api/tx/buy/0" },
    { "label": "NO ($1)", "action": "tx", "target": "/api/tx/buy/1" },
    { "label": "View Market", "action": "link", "target": "https://truthyfi.xyz/market/:id" }
  ]
}
```

**Benefits:**
- Bet without leaving Farcaster
- Share predictions virally
- Build credibility through on-chain history
- Reach 300k+ Farcaster users

## 💰 Tokenomics

### Fees

- **Market Creation**: $5 USDC (prevents spam)
- **Trading Fee**: 2% on buys and sells
- **Winning Redemption**: 0% fee
- **Fee Distribution**: 100% to protocol (upgradeable)

### Market Economics

- **Min Bet**: $0.50 USDC
- **Max Bet**: $1,000 USDC (prevents whale manipulation)
- **Initial Liquidity**: Creator-provided (min $100)
- **Pricing**: Automated market maker (supply-based)

### Future Revenue

- Protocol fees → DAO treasury
- Premium features (analytics, API access)
- Market maker incentives
- Cross-chain expansion

## 🛡 Security

### Implemented Protections

- ✅ **OpenZeppelin Contracts**: Battle-tested base contracts
- ✅ **ReentrancyGuard**: Prevents reentrancy attacks
- ✅ **Pausable**: Emergency stop functionality
- ✅ **SafeERC20**: Safe token transfers
- ✅ **Access Control**: Owner/resolver separation
- ✅ **Input Validation**: All user inputs validated
- ✅ **Bet Limits**: Prevents excessive exposure

### Audit Status

- ⏳ **Internal Review**: In progress
- ⏳ **External Audit**: Planned (post-testnet)
- ⏳ **Bug Bounty**: Launching with mainnet

### Planned Improvements

- [ ] Slither static analysis
- [ ] Echidna fuzzing
- [ ] Formal verification
- [ ] Multi-sig governance
- [ ] Timelock for critical operations
- [ ] Oracle integration (Chainlink, UMA)

## 📈 Roadmap

### Phase 1: MVP (Week 1) ✅
- [x] Smart contract development
- [x] USDC integration
- [x] Security features
- [x] Comprehensive tests
- [x] Deployment scripts
- [ ] Deploy to Base Sepolia
- [ ] Basic frontend
- [ ] Farcaster Frame

### Phase 2: Testnet Launch (Week 2-3)
- [ ] Deploy demo markets
- [ ] Community testing
- [ ] Bug fixes and optimizations
- [ ] Documentation
- [ ] Grant applications

### Phase 3: Mainnet Preparation (Week 4-6)
- [ ] External audit
- [ ] Bug bounty program
- [ ] Advanced frontend features
- [ ] Mobile app (PWA)
- [ ] Marketing materials

### Phase 4: Mainnet Launch
- [ ] Deploy to Base Mainnet
- [ ] Launch marketing campaign
- [ ] Partnerships (Farcaster, Base)
- [ ] Liquidity incentives
- [ ] DAO formation

### Phase 5: Growth
- [ ] Multi-outcome markets (not just binary)
- [ ] Oracle integration (UMA, Chainlink)
- [ ] Automated resolution
- [ ] Liquidity mining
- [ ] Cross-chain expansion (Optimism, Arbitrum)
- [ ] Mobile native apps
- [ ] Advanced analytics
- [ ] API for developers
- [ ] White-label solutions

## 🎁 Grant Applications

TruthyFi is applying for:

1. **Base Ecosystem Fund** ($10-50k)
   - Social consumer app on Base
   - Novel use case for L2

2. **Farcaster Ecosystem** ($5-20k)
   - Innovative Frame implementation
   - Social graph integration

3. **Coinbase Ventures** ($100-500k)
   - "Onchain is the new online" thesis
   - Social + DeFi hybrid

### Why Fund TruthyFi?

- ✅ **First social prediction market on Base**
- ✅ **Leverages Coinbase Smart Wallet** (passkey login, gasless tx)
- ✅ **Farcaster-native** (300k+ users)
- ✅ **Solves credibility crisis** (skin in the game)
- ✅ **Micro-bets** = mass adoption ($0.50 entry)
- ✅ **Production-ready code** (tested, secure)
- ✅ **Clear revenue model** (protocol fees)
- ✅ **Experienced team** (list your background)

## 🤝 Contributing

We welcome contributions! Please:

1. Fork the repo
2. Create a feature branch
3. Write tests for new functionality
4. Ensure all tests pass
5. Submit a pull request

### Development Guidelines

- Follow Solidity style guide
- Add NatSpec documentation
- Maintain test coverage >80%
- Gas optimize where possible
- No breaking changes without discussion

## 📄 License

UNLICENSED - Proprietary (will open source post-audit)

## 🔗 Links

- **Website**: https://truthyfi.xyz (coming soon)
- **Twitter**: https://twitter.com/truthyfi (coming soon)
- **Farcaster**: https://warpcast.com/truthyfi (coming soon)
- **Discord**: https://discord.gg/truthyfi (coming soon)
- **Docs**: https://docs.truthyfi.xyz (coming soon)

## 📞 Contact

- **Email**: team@truthyfi.xyz
- **Telegram**: @truthyfi

---

**Built with ❤️ on Base** | Powered by Foundry | Integrated with Farcaster

*Put your money where your mouth is* 💰
