# TruthyFi Automation Scripts

Helper scripts for local testing, demos, and automation.

---

## 🚀 Quick Start

```bash
# Start local test environment (automated)
bash scripts/local-test.sh

# Run a demo trading flow
bash scripts/demo.sh

# Stop local environment
bash scripts/stop-local.sh
```

---

## 📁 Available Scripts

### local-test.sh

**Automated local testing setup** - Sets up complete local environment in one command.

**What it does:**
1. ✅ Starts Anvil (local blockchain)
2. ✅ Deploys all contracts
3. ✅ Verifies deployment
4. ✅ Creates 5 demo markets
5. ✅ Tests trading functionality
6. ✅ Installs frontend dependencies
7. ✅ Configures frontend with local addresses

**Usage:**
```bash
bash scripts/local-test.sh
```

**Output:**
```
🚀 TruthyFi Local Testing Setup
================================

✅ Prerequisites check passed
📦 Starting local blockchain (Anvil)...
✅ Anvil running on http://localhost:8545

📝 Default Test Account:
  Address: 0xf39Fd6e51aad88F6F4ce6aB8827279cffFb92266
  Private Key: 0xac097...

🔨 Building contracts...
✅ Contracts built

🚀 Deploying contracts...
✅ Contracts deployed
  Factory: 0xe7f1725...
  USDC: 0x5FbDB2315...

✅ Verifying deployment...
✅ ALL CHECKS PASSED

📊 Creating demo markets...
✅ Demo markets created

💰 Testing trading functionality...
✅ Trading test passed

🌐 Setting up frontend...
✅ Frontend configured

================================
🎉 Setup Complete!
================================
```

**Time:** ~2 minutes

**Requirements:**
- Foundry installed
- Node.js v18+
- Port 8545 available

---

### demo.sh

**Interactive demo script** - Demonstrates complete trading flow.

**What it does:**
1. ✅ Gets test USDC from faucet
2. ✅ Approves USDC for market
3. ✅ Buys 10 YES tokens
4. ✅ Shows price impact
5. ✅ Sells 5 YES tokens
6. ✅ Displays final position

**Usage:**
```bash
# Run after local-test.sh
bash scripts/demo.sh
```

**Output:**
```
🎬 TruthyFi Demo Script
=======================

📊 Demo Setup:
  Factory: 0xe7f1725...
  USDC: 0x5FbDB2315...
  Trader: 0xf39Fd6e5...

📈 Market Information:
  Name: Will ETH reach $5000 by year end?
  YES Price: 50.00%
  NO Price: 50.00%

💰 Getting test USDC...
  USDC Balance: 1000.00 USDC

✅ Approving USDC...
  Approved!

🛒 Buying 10 YES tokens...
  Estimated cost: 5.10 USDC
  ✅ Purchase complete!

📊 Updated Prices:
  YES Price: 52.45% (was 50.00%)
  NO Price: 47.55% (was 50.00%)
  Price Impact: +4.90%

💼 Your Position:
  YES Tokens: 10.00
  Entry Price: 50.00%
  Current Price: 52.45%

💸 Selling 5 YES tokens...
  Estimated proceeds: 2.62 USDC
  ✅ Sale complete!

📊 Final Prices:
  YES Price: 51.20%
  NO Price: 48.80%

💼 Final Position:
  YES Tokens: 5.00
  USDC Balance: 997.52 USDC

✅ Demo Complete!
```

**Time:** ~30 seconds

**Requirements:**
- Anvil running (via local-test.sh)
- Contracts deployed
- Markets created

---

### stop-local.sh

**Cleanup script** - Stops Anvil and cleans up resources.

**What it does:**
1. ✅ Stops Anvil process
2. ✅ Frees port 8545
3. ✅ Cleans up log files
4. ✅ Removes PID files

**Usage:**
```bash
bash scripts/stop-local.sh
```

**Output:**
```
🛑 Stopping TruthyFi Local Test Environment
===========================================

Stopping Anvil (PID: 12345)...
✅ Anvil stopped
✅ Logs cleaned
✅ Cleanup complete!
```

---

## 🎯 Common Workflows

### 1. Full Local Testing Setup

```bash
# One-command setup
bash scripts/local-test.sh

# In another terminal, start frontend
cd frontend
npm run dev

# Open http://localhost:3000 in browser
```

### 2. Quick Demo for Presentation

```bash
# Start environment
bash scripts/local-test.sh

# Wait for setup to complete (~2 min)

# Run demo
bash scripts/demo.sh

# Show in UI
cd frontend && npm run dev
# Open http://localhost:3000
```

### 3. Development Workflow

```bash
# Start Anvil only
anvil

# Deploy manually (in another terminal)
forge script script/Deploy.s.sol:DeployScript \
  --rpc-url http://localhost:8545 \
  --broadcast

# Iterate on contracts
# ... make changes ...
forge build
forge script script/Deploy.s.sol:DeployScript \
  --rpc-url http://localhost:8545 \
  --broadcast

# Test changes
forge test
```

### 4. Cleanup and Restart

```bash
# Stop everything
bash scripts/stop-local.sh

# Restart fresh
bash scripts/local-test.sh
```

---

## 🔧 Script Details

### Environment Variables

Scripts automatically set these variables:

```bash
PRIVATE_KEY=0xac0974bec39a17e36ba4a6b4d238ff944bacb478cbed5efcae784d7bf4f2ff80
FACTORY_ADDRESS=<from_deployment>
USDC_ADDRESS=<from_deployment>
```

### Default Anvil Account

All scripts use Anvil's first default account:

```
Address: 0xf39Fd6e51aad88F6F4ce6aB8827279cffFb92266
Private Key: 0xac0974bec39a17e36ba4a6b4d238ff944bacb478cbed5efcae784d7bf4f2ff80
Balance: 10,000 ETH
```

**Import to MetaMask:**
1. Open MetaMask
2. Click account icon → Import Account
3. Select "Private Key"
4. Paste: `0xac0974bec39a17e36ba4a6b4d238ff944bacb478cbed5efcae784d7bf4f2ff80`

### Network Configuration

**Local Network (Anvil):**
- Network Name: `Localhost`
- RPC URL: `http://localhost:8545`
- Chain ID: `31337`
- Currency Symbol: `ETH`

---

## 📝 Script Output Files

Scripts create these files:

```
/tmp/anvil.log              # Anvil logs
/tmp/truthy-anvil.pid       # Anvil process ID
deployments/31337.json      # Deployment addresses
frontend/src/config/contracts.local.ts  # Frontend config
```

---

## 🐛 Troubleshooting

### "Port 8545 already in use"

```bash
# Kill existing process
bash scripts/stop-local.sh

# Or manually
kill -9 $(lsof -t -i:8545)
```

### "Anvil not found"

```bash
# Install Foundry
curl -L https://foundry.paradigm.xyz | bash
foundryup
```

### "Node.js not found"

```bash
# Install Node.js from https://nodejs.org/
# Or using nvm:
curl -o- https://raw.githubusercontent.com/nvm-sh/nvm/v0.39.0/install.sh | bash
nvm install 18
nvm use 18
```

### "Deployment failed"

```bash
# Check Anvil is running
curl -X POST http://localhost:8545 \
  -H "Content-Type: application/json" \
  -d '{"jsonrpc":"2.0","method":"eth_blockNumber","params":[],"id":1}'

# Should return block number

# Restart Anvil
bash scripts/stop-local.sh
anvil
```

### "No markets found"

```bash
# Create markets manually
forge script script/CreateDemoMarket.s.sol:CreateDemoMarket \
  --rpc-url http://localhost:8545 \
  --broadcast
```

---

## 🎨 Customization

### Change Demo Markets

Edit `script/CreateDemoMarket.s.sol` to create custom markets:

```solidity
factory.createMarket(
    keccak256("your-market-id"),
    "Your Market Question?",
    "Your market description",
    "YourCategory",
    "https://source-url.com",
    address(this),
    block.timestamp + 30 days,
    [uint256(0.5e18), 0.5e18],
    2000e6
);
```

### Change Initial Liquidity

Edit `script/CreateDemoMarket.s.sol`:

```solidity
uint256 initialLiquidity = 5000e6; // 5000 USDC instead of 2000
```

### Change Test Account

Edit scripts to use different Anvil account:

```bash
# Anvil provides 10 accounts
# See full list when you run: anvil

# Use account #2 instead
export PRIVATE_KEY=0x59c6995e998f97a5a0044966f0945389dc9e86dae88c7a8412f4603b6b78690d
```

---

## 🚀 Advanced Usage

### Run Multiple Test Scenarios

```bash
# Scenario 1: Heavy YES buying
forge script script/TestTrading.s.sol:TestTrading \
  --rpc-url http://localhost:8545 \
  --broadcast

# Scenario 2: Create user market
cast send $FACTORY_ADDRESS \
  "createMarket(...)" \
  --rpc-url http://localhost:8545 \
  --private-key $PRIVATE_KEY

# Scenario 3: Resolve market
cast send $MARKET_ADDRESS \
  "resolve(uint256)" 0 \
  --rpc-url http://localhost:8545 \
  --private-key $PRIVATE_KEY
```

### Automated Testing Loop

```bash
#!/bin/bash
# Test multiple iterations
for i in {1..10}; do
  echo "Test iteration $i"
  bash scripts/demo.sh
  sleep 2
done
```

### Continuous Monitoring

```bash
# Monitor in real-time
watch -n 5 'forge script script/MonitorHealth.s.sol:MonitorHealth --rpc-url http://localhost:8545'
```

---

## 📚 Related Documentation

- [LOCAL_TESTING_GUIDE.md](../LOCAL_TESTING_GUIDE.md) - Complete local testing guide
- [DEPLOYMENT_RUNBOOK.md](../DEPLOYMENT_RUNBOOK.md) - Production deployment
- [PROJECT_STATUS.md](../PROJECT_STATUS.md) - Project overview

---

## 🆘 Support

If scripts fail or you encounter issues:

1. Check Anvil logs: `tail -f /tmp/anvil.log`
2. Verify Foundry version: `forge --version`
3. Clean restart: `bash scripts/stop-local.sh && bash scripts/local-test.sh`
4. Check [Troubleshooting](#troubleshooting) section above

---

**Happy Testing! 🚀**
