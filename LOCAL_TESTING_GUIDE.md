# TruthyFi Local Testing Guide

Complete guide for running TruthyFi locally for testing and demo purposes.

---

## 📋 Table of Contents

1. [Quick Start (5 minutes)](#quick-start)
2. [Option 1: Local Network (Anvil)](#option-1-local-network-anvil)
3. [Option 2: Base Sepolia Testnet](#option-2-base-sepolia-testnet)
4. [Frontend Setup](#frontend-setup)
5. [Testing the Full Flow](#testing-the-full-flow)
6. [Demo Script](#demo-script)
7. [Troubleshooting](#troubleshooting)

---

## Quick Start

```bash
# 1. Clone and install
git clone <repo-url>
cd truthy-contracts
forge install

# 2. Start local blockchain
anvil

# 3. Deploy contracts (new terminal)
forge script script/Deploy.s.sol:DeployScript \
  --rpc-url http://localhost:8545 \
  --broadcast

# 4. Set up frontend (new terminal)
cd frontend
npm install
npm run dev

# 5. Open http://localhost:3000
```

---

## Option 1: Local Network (Anvil)

### Step 1: Install Foundry

```bash
# Install Foundry
curl -L https://foundry.paradigm.xyz | bash

# Restart terminal, then install Foundry tools
foundryup

# Verify installation
forge --version
anvil --version
cast --version
```

### Step 2: Start Local Blockchain

```bash
# Start Anvil (local Ethereum node)
# This runs on http://localhost:8545
anvil

# Keep this terminal running!
```

**Anvil provides:**
- 10 test accounts with 10,000 ETH each
- Instant block mining
- Perfect for local testing

**Default test account (use this for deployment):**
```
Address: 0xf39Fd6e51aad88F6F4ce6aB8827279cffFb92266
Private Key: 0xac0974bec39a17e36ba4a6b4d238ff944bacb478cbed5efcae784d7bf4f2ff80
```

### Step 3: Deploy Contracts Locally

Open a new terminal:

```bash
# Set up environment variables
export PRIVATE_KEY=0xac0974bec39a17e36ba4a6b4d238ff944bacb478cbed5efcae784d7bf4f2ff80
export FACTORY_ADDRESS=""
export USDC_ADDRESS=""

# Deploy to local network
forge script script/Deploy.s.sol:DeployScript \
  --rpc-url http://localhost:8545 \
  --broadcast \
  -vvvv
```

**Save the output addresses:**
```bash
# Example output:
MockUSDC deployed at: 0x5FbDB2315678afecb367f032d93F642f64180aa3
TruthyMarketFactory deployed at: 0xe7f1725E7734CE288F8367e1Bb143E90bb3F0512

# Save these for later use
export USDC_ADDRESS=0x5FbDB2315678afecb367f032d93F642f64180aa3
export FACTORY_ADDRESS=0xe7f1725E7734CE288F8367e1Bb143E90bb3F0512
```

### Step 4: Verify Deployment

```bash
# Run verification script
forge script script/PostDeploymentCheck.s.sol:PostDeploymentCheck \
  --rpc-url http://localhost:8545

# Should output: "✅ ALL CHECKS PASSED - DEPLOYMENT VERIFIED!"
```

### Step 5: Create Demo Markets

```bash
# Create 5 sample markets
forge script script/CreateDemoMarket.s.sol:CreateDemoMarket \
  --rpc-url http://localhost:8545 \
  --broadcast \
  -vvv

# Verify markets were created
forge script script/VerifyDeployment.s.sol:VerifyDeployment \
  --rpc-url http://localhost:8545
```

### Step 6: Test Trading

```bash
# Run interactive trading test
forge script script/TestTrading.s.sol:TestTrading \
  --rpc-url http://localhost:8545 \
  --broadcast \
  -vvv

# Should output: "✅ Trading test completed successfully!"
```

---

## Option 2: Base Sepolia Testnet

### Step 1: Get Base Sepolia ETH

Visit the Base faucet:
- https://www.coinbase.com/faucets/base-ethereum-goerli-faucet
- Or use: https://faucet.quicknode.com/base/sepolia

You need ~0.1 ETH for deployment and testing.

### Step 2: Set Up Environment

Create `.env` file:

```bash
# .env
PRIVATE_KEY=your_private_key_here
BASE_SEPOLIA_RPC=https://sepolia.base.org
BASESCAN_API_KEY=your_basescan_api_key  # Optional, for verification
```

**⚠️ Never commit your .env file!**

### Step 3: Deploy to Base Sepolia

```bash
# Load environment
source .env

# Deploy
forge script script/Deploy.s.sol:DeployScript \
  --rpc-url $BASE_SEPOLIA_RPC \
  --broadcast \
  --verify \
  -vvvv

# Save deployment addresses
export FACTORY_ADDRESS=<factory_address_from_output>
export USDC_ADDRESS=<usdc_address_from_output>
```

### Step 4: Verify Deployment

```bash
forge script script/PostDeploymentCheck.s.sol:PostDeploymentCheck \
  --rpc-url $BASE_SEPOLIA_RPC
```

### Step 5: Create Demo Markets

```bash
forge script script/CreateDemoMarket.s.sol:CreateDemoMarket \
  --rpc-url $BASE_SEPOLIA_RPC \
  --broadcast
```

### Step 6: View on BaseScan

Visit BaseScan to see your deployed contracts:
- Factory: `https://sepolia.basescan.org/address/<FACTORY_ADDRESS>`
- View all transactions and events

---

## Frontend Setup

### Step 1: Install Dependencies

```bash
cd frontend
npm install
```

### Step 2: Configure Contract Addresses

Edit `frontend/src/config/contracts.ts`:

**For Local Network (Anvil):**
```typescript
export const CONTRACTS = {
  31337: { // Anvil chain ID
    factory: '0xe7f1725E7734CE288F8367e1Bb143E90bb3F0512', // Your factory address
    usdc: '0x5FbDB2315678afecb367f032d93F642f64180aa3',    // Your USDC address
  },
}
```

**For Base Sepolia:**
```typescript
export const CONTRACTS = {
  84532: { // Base Sepolia chain ID
    factory: '0x...', // Your deployed factory address
    usdc: '0x...',    // Your deployed USDC address
  },
}
```

### Step 3: Configure Wagmi for Local Network

Edit `frontend/src/config/wagmi.ts`:

```typescript
import { Chain } from 'wagmi/chains'

// Add local network
export const localhost = {
  id: 31337,
  name: 'Localhost',
  network: 'localhost',
  nativeCurrency: {
    decimals: 18,
    name: 'Ether',
    symbol: 'ETH',
  },
  rpcUrls: {
    default: { http: ['http://127.0.0.1:8545'] },
    public: { http: ['http://127.0.0.1:8545'] },
  },
} as const satisfies Chain

// Add to config
export const config = createConfig({
  chains: [baseSepolia, localhost], // Add localhost
  // ... rest of config
})
```

### Step 4: Start Frontend

```bash
# Development mode (with hot reload)
npm run dev

# Build for production
npm run build
npm start
```

Open http://localhost:3000

### Step 5: Connect Wallet

1. Open MetaMask
2. Add network:
   - **For Anvil**:
     - Network Name: Localhost
     - RPC URL: http://localhost:8545
     - Chain ID: 31337
     - Currency Symbol: ETH
   - **For Base Sepolia**:
     - Click "Add Network" → "Base Sepolia"
3. Import test account (Anvil only):
   - Use private key: `0xac0974bec39a17e36ba4a6b4d238ff944bacb478cbed5efcae784d7bf4f2ff80`
4. Connect wallet to app

---

## Testing the Full Flow

### Complete End-to-End Test

```bash
#!/bin/bash
# save as test-local.sh and run: bash test-local.sh

echo "🚀 Starting TruthyFi Local Test"

# 1. Start Anvil in background
echo "📦 Starting local blockchain..."
anvil > /tmp/anvil.log 2>&1 &
ANVIL_PID=$!
sleep 3

# 2. Deploy contracts
echo "🔨 Deploying contracts..."
export PRIVATE_KEY=0xac0974bec39a17e36ba4a6b4d238ff944bacb478cbed5efcae784d7bf4f2ff80
forge script script/Deploy.s.sol:DeployScript \
  --rpc-url http://localhost:8545 \
  --broadcast

# 3. Get addresses from deployment
export FACTORY_ADDRESS=$(cat deployments/31337.json | jq -r '.factory')
export USDC_ADDRESS=$(cat deployments/31337.json | jq -r '.usdc')

echo "Factory: $FACTORY_ADDRESS"
echo "USDC: $USDC_ADDRESS"

# 4. Verify deployment
echo "✅ Verifying deployment..."
forge script script/PostDeploymentCheck.s.sol:PostDeploymentCheck \
  --rpc-url http://localhost:8545

# 5. Create demo markets
echo "📊 Creating demo markets..."
forge script script/CreateDemoMarket.s.sol:CreateDemoMarket \
  --rpc-url http://localhost:8545 \
  --broadcast

# 6. Test trading
echo "💰 Testing trading..."
forge script script/TestTrading.s.sol:TestTrading \
  --rpc-url http://localhost:8545 \
  --broadcast

echo ""
echo "✅ All tests passed!"
echo "Factory Address: $FACTORY_ADDRESS"
echo "USDC Address: $USDC_ADDRESS"
echo ""
echo "Now run: cd frontend && npm run dev"
echo "Then visit: http://localhost:3000"
echo ""
echo "To stop Anvil: kill $ANVIL_PID"
```

### Manual Testing in Frontend

1. **Browse Markets**
   - Visit http://localhost:3000
   - See all created markets
   - Filter by category

2. **View Market Details**
   - Click on any market
   - See current YES/NO prices
   - View market metadata

3. **Get Test USDC** (Local only)
   ```bash
   # Get USDC from faucet (1000 USDC)
   cast send $USDC_ADDRESS \
     "faucet()" \
     --rpc-url http://localhost:8545 \
     --private-key $PRIVATE_KEY

   # Check balance
   cast call $USDC_ADDRESS \
     "balanceOf(address)(uint256)" \
     0xf39Fd6e51aad88F6F4ce6aB8827279cffFb92266 \
     --rpc-url http://localhost:8545
   ```

4. **Make a Trade**
   - Select market
   - Choose YES or NO
   - Enter amount (min 0.5 USDC)
   - Approve USDC (first time)
   - Execute trade
   - See updated prices

5. **Check Your Position**
   - View your outcome tokens
   - See unrealized P&L
   - Track your trades

---

## Demo Script

Perfect for showing TruthyFi to others:

### 5-Minute Demo

```bash
# 1. Start everything
anvil &
sleep 3
forge script script/Deploy.s.sol:DeployScript --rpc-url http://localhost:8545 --broadcast
export FACTORY_ADDRESS=<from_output>
export USDC_ADDRESS=<from_output>
forge script script/CreateDemoMarket.s.sol:CreateDemoMarket --rpc-url http://localhost:8545 --broadcast

# 2. Start frontend
cd frontend
npm run dev

# 3. Show to audience:
# - Market discovery page
# - Click on "Will ETH reach $5000?"
# - Show current odds (50/50)
# - Make a trade on YES
# - Watch odds update
# - Show position tracking
```

### Demo Markets Created

1. **Crypto** - Will ETH reach $5000 by year end?
2. **Politics** - Will [Candidate] win 2024 election?
3. **Crypto** - Will Bitcoin hit $100k by Q4?
4. **DeFi** - Will Base TVL exceed $10B by end of year?
5. **Tech** - Will Farcaster reach 1M users by year end?

---

## Troubleshooting

### Anvil Won't Start

```bash
# Check if port 8545 is in use
lsof -i :8545

# Kill existing process
kill -9 <PID>

# Start Anvil on different port
anvil --port 8546
# Update RPC URL: http://localhost:8546
```

### Deployment Fails

```bash
# Check Anvil is running
curl -X POST http://localhost:8545 \
  -H "Content-Type: application/json" \
  -d '{"jsonrpc":"2.0","method":"eth_blockNumber","params":[],"id":1}'

# Should return: {"jsonrpc":"2.0","id":1,"result":"0x0"}

# Check balance
cast balance 0xf39Fd6e51aad88F6F4ce6aB8827279cffFb92266 --rpc-url http://localhost:8545

# Should show: 10000000000000000000000 (10,000 ETH)
```

### Frontend Won't Connect

```bash
# Check MetaMask is on correct network
# Network should be: Localhost (Chain ID: 31337)

# Check contract addresses in frontend/src/config/contracts.ts
# Must match deployed addresses

# Clear browser cache and restart
```

### "Insufficient Allowance" Error

```bash
# Approve USDC spending
cast send $USDC_ADDRESS \
  "approve(address,uint256)" \
  <MARKET_ADDRESS> \
  $(cast max-uint256) \
  --rpc-url http://localhost:8545 \
  --private-key $PRIVATE_KEY

# Frontend should handle this automatically
```

### Markets Not Showing

```bash
# Check markets were created
forge script script/VerifyDeployment.s.sol:VerifyDeployment \
  --rpc-url http://localhost:8545

# Check factory address in frontend config
# Should match deployed factory

# Check console for errors
# Open browser DevTools → Console
```

### "Market Expired" Error

```bash
# Demo markets expire in 30 days
# For testing, modify CreateDemoMarket.s.sol:
# expiresAt: block.timestamp + 30 days
# Change to: block.timestamp + 365 days

# Redeploy markets
forge script script/CreateDemoMarket.s.sol:CreateDemoMarket \
  --rpc-url http://localhost:8545 \
  --broadcast
```

---

## Using Cast for Testing

Cast is a powerful CLI tool for interacting with contracts:

```bash
# Get market count
cast call $FACTORY_ADDRESS \
  "getTotalMarkets()(uint256)" \
  --rpc-url http://localhost:8545

# Get all markets
cast call $FACTORY_ADDRESS \
  "getAllMarkets()(address[])" \
  --rpc-url http://localhost:8545

# Get market price
MARKET_ADDRESS=0x...
cast call $MARKET_ADDRESS \
  "getOutcomePrice(uint256)(uint256)" \
  0 \
  --rpc-url http://localhost:8545

# Buy outcome (need approval first)
cast send $MARKET_ADDRESS \
  "buyOutcome(uint256,uint256)" \
  0 \
  10000000000000000000 \
  --rpc-url http://localhost:8545 \
  --private-key $PRIVATE_KEY

# Sell outcome
cast send $MARKET_ADDRESS \
  "sellOutcome(uint256,uint256)" \
  0 \
  5000000000000000000 \
  --rpc-url http://localhost:8545 \
  --private-key $PRIVATE_KEY
```

---

## Monitoring Local Chain

### View Logs

```bash
# Anvil logs (if running in background)
tail -f /tmp/anvil.log

# Get latest block
cast block-number --rpc-url http://localhost:8545

# Get block info
cast block latest --rpc-url http://localhost:8545

# Get transaction receipt
cast receipt <TX_HASH> --rpc-url http://localhost:8545
```

### Monitor Health

```bash
# Run health check
forge script script/MonitorHealth.s.sol:MonitorHealth \
  --rpc-url http://localhost:8545

# Shows:
# - Total markets
# - Active/resolved counts
# - Total liquidity
# - Total volume
# - Most active market
```

---

## Clean Restart

If things get messy, start fresh:

```bash
# 1. Stop Anvil
killall anvil

# 2. Clean build artifacts
forge clean

# 3. Remove deployments
rm -rf deployments/

# 4. Restart Anvil
anvil

# 5. Redeploy everything
forge script script/Deploy.s.sol:DeployScript \
  --rpc-url http://localhost:8545 \
  --broadcast

forge script script/CreateDemoMarket.s.sol:CreateDemoMarket \
  --rpc-url http://localhost:8545 \
  --broadcast

# 6. Restart frontend
cd frontend
rm -rf .next
npm run dev
```

---

## Production Testing on Base Sepolia

For more realistic testing:

```bash
# 1. Deploy to Base Sepolia
source .env
forge script script/Deploy.s.sol:DeployScript \
  --rpc-url $BASE_SEPOLIA_RPC \
  --broadcast \
  --verify

# 2. Create markets
forge script script/CreateDemoMarket.s.sol:CreateDemoMarket \
  --rpc-url $BASE_SEPOLIA_RPC \
  --broadcast

# 3. Update frontend config with testnet addresses
# Edit frontend/src/config/contracts.ts

# 4. Deploy frontend to Vercel
cd frontend
vercel deploy

# 5. Share link with testers!
```

---

## Tips for Demos

1. **Prepare in advance**: Deploy and create markets before demo
2. **Use Base Sepolia**: More impressive than localhost
3. **Pre-fund wallets**: Have test USDC ready
4. **Show mobile**: Frontend is responsive
5. **Explain features**:
   - Permissionless market creation
   - Social metadata (categories, sources)
   - Real-time price updates
   - Low fees ($0.21 average)
   - Farcaster integration

---

## Next Steps

- ✅ Test locally with Anvil
- ✅ Deploy to Base Sepolia
- ✅ Test full trading flow
- ✅ Create custom markets
- ✅ Invite friends to test
- ✅ Gather feedback
- ⏭️ Plan mainnet launch!

---

## Resources

- [Foundry Book](https://book.getfoundry.sh/)
- [Anvil Documentation](https://book.getfoundry.sh/anvil/)
- [Cast Commands](https://book.getfoundry.sh/cast/)
- [Base Documentation](https://docs.base.org/)
- [Project Documentation](./PROJECT_STATUS.md)

---

**Happy Testing! 🚀**

For issues, check [DEPLOYMENT_RUNBOOK.md](./DEPLOYMENT_RUNBOOK.md) or create an issue on GitHub.
