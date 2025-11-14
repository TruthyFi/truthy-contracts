# TruthyFi Deployment Scripts

Comprehensive automation scripts for deploying, managing, and monitoring TruthyFi smart contracts.

---

## 📋 Script Overview

| Script | Purpose | When to Use |
|--------|---------|-------------|
| `Deploy.s.sol` | Deploy Factory and USDC | Initial deployment |
| `PostDeploymentCheck.s.sol` | Comprehensive verification | After deployment |
| `VerifyDeployment.s.sol` | Quick verification | Quick health check |
| `CreateDemoMarket.s.sol` | Create sample markets | Testing, demos |
| `TestTrading.s.sol` | Test trading flow | Verify trading works |
| `MonitorHealth.s.sol` | System health monitoring | Daily/weekly monitoring |
| `BatchResolve.s.sol` | Resolve multiple markets | Market resolution |
| `WithdrawFees.s.sol` | Withdraw protocol fees | Fee collection |
| `EmergencyPause.s.sol` | Pause all markets | Security emergencies |
| `EmergencyUnpause.s.sol` | Resume operations | After emergency fix |

---

## 🚀 Quick Start

### 1. Initial Deployment

```bash
# Set up environment
cp .env.example .env
# Edit .env with your private key and RPC URLs

# Deploy to Base Sepolia
forge script script/Deploy.s.sol:DeployScript \
  --rpc-url base_sepolia \
  --broadcast \
  --verify

# Save the factory and USDC addresses to .env
```

### 2. Verify Deployment

```bash
# Run comprehensive checks
forge script script/PostDeploymentCheck.s.sol:PostDeploymentCheck \
  --rpc-url base_sepolia

# Should output: "✅ ALL CHECKS PASSED - DEPLOYMENT VERIFIED!"
```

### 3. Create Demo Markets

```bash
forge script script/CreateDemoMarket.s.sol:CreateDemoMarket \
  --rpc-url base_sepolia \
  --broadcast
```

### 4. Test Trading

```bash
forge script script/TestTrading.s.sol:TestTrading \
  --rpc-url base_sepolia \
  --broadcast
```

---

## 📖 Detailed Script Documentation

### Deploy.s.sol

**Purpose**: Deploy TruthyMarketFactory and USDC contracts.

**Configuration**:
- `CREATION_FEE`: 5 USDC (5e6)
- `PROTOCOL_FEE_RATE`: 2% (200 basis points)

**Networks**:
- Base Sepolia (84532): Deploys MockUSDC
- Base Mainnet (8453): Uses real USDC at `0x833589fCD6eDb6E08f4c7C32D4f71b54bdA02913`
- Other: Deploys MockUSDC

**Output**: Saves deployment info to `deployments/{chainId}.json`

**Usage**:
```bash
forge script script/Deploy.s.sol:DeployScript \
  --rpc-url $RPC_URL \
  --broadcast \
  --verify \
  -vvvv
```

---

### PostDeploymentCheck.s.sol

**Purpose**: Comprehensive post-deployment verification with 25+ checks.

**Checks**:
- ✅ Factory configuration (fees, owner, token)
- ✅ USDC integration
- ✅ Factory functions (queries, tracking)
- ✅ Market configuration (metadata, settings)
- ✅ Market trading (prices, previews)
- ✅ Gas optimizations
- ✅ Security features

**Output**: Detailed report with pass/fail for each check.

**Usage**:
```bash
# Requires FACTORY_ADDRESS and USDC_ADDRESS in .env
forge script script/PostDeploymentCheck.s.sol:PostDeploymentCheck \
  --rpc-url $RPC_URL
```

**Expected Output**:
```
========================================
POST-DEPLOYMENT VERIFICATION
========================================
...
✅ Factory has payment token
✅ Payment token matches USDC
✅ Creation fee is reasonable
...
========================================
VERIFICATION SUMMARY
========================================
Total Checks: 25
Passed: 25
Failed: 0

✅ ALL CHECKS PASSED - DEPLOYMENT VERIFIED!
```

---

### VerifyDeployment.s.sol

**Purpose**: Quick verification of factory and market configuration.

**Checks**:
- Factory payment token, fees, owner
- Market metadata if markets exist

**Usage**:
```bash
forge script script/VerifyDeployment.s.sol:VerifyDeployment \
  --rpc-url $RPC_URL
```

---

### CreateDemoMarket.s.sol

**Purpose**: Create 5 sample prediction markets for testing.

**Markets Created**:
1. **Crypto**: Will ETH reach $5000?
2. **Politics**: Will [Candidate] win 2024 election?
3. **Crypto**: Will Bitcoin hit $100k?
4. **DeFi**: Will Base TVL exceed $10B?
5. **Tech**: Will Farcaster reach 1M users?

**Liquidity**: $2000 USDC per market
**Initial Prices**: 50/50 split

**Usage**:
```bash
forge script script/CreateDemoMarket.s.sol:CreateDemoMarket \
  --rpc-url base_sepolia \
  --broadcast
```

---

### TestTrading.s.sol

**Purpose**: Interactive script to test trading functionality.

**Steps**:
1. Get test USDC from faucet (testnet only)
2. Select first available market
3. Approve USDC spending
4. Buy 10 YES outcome tokens
5. Display updated prices

**Usage**:
```bash
forge script script/TestTrading.s.sol:TestTrading \
  --rpc-url base_sepolia \
  --broadcast
```

---

### MonitorHealth.s.sol

**Purpose**: Monitor system health and status.

**Displays**:
- **Factory Health**: Total markets, fees, owner
- **Market Health**: Active/expired/resolved counts, liquidity, volume
- **Financial Metrics**: Total fees, protocol revenue
- **User Activity**: Most active market
- **Alerts**: Expired markets, low liquidity warnings

**Recommended**: Run daily or weekly via cron.

**Usage**:
```bash
forge script script/MonitorHealth.s.sol:MonitorHealth \
  --rpc-url $RPC_URL
```

**Cron Example**:
```bash
# Run every 6 hours
0 */6 * * * cd /path/to/truthy-contracts && forge script script/MonitorHealth.s.sol...
```

---

### BatchResolve.s.sol

**Purpose**: Batch resolve multiple expired markets efficiently.

**Process**:
1. Scans all markets for expired, unresolved ones
2. Displays each with current prices
3. **MANUAL STEP**: Review and set winning outcomes
4. Uncomment resolution code
5. Execute batch resolution

**Usage**:
```bash
# Step 1: Scan for expired markets
forge script script/BatchResolve.s.sol:BatchResolve \
  --rpc-url $RPC_URL

# Step 2: Review output and modify script with outcomes
# Example:
#   expiredMarkets[0].winningOutcome = 0; // YES wins
#   expiredMarkets[1].winningOutcome = 1; // NO wins

# Step 3: Uncomment resolution code in script

# Step 4: Run with broadcast to resolve
forge script script/BatchResolve.s.sol:BatchResolve \
  --rpc-url $RPC_URL \
  --broadcast
```

---

### WithdrawFees.s.sol

**Purpose**: Withdraw accumulated fees from factory and all markets.

**Withdraws**:
- Factory creation fees
- All market trading fees

**Requires**: `FEE_RECIPIENT` address in .env

**Usage**:
```bash
forge script script/WithdrawFees.s.sol:WithdrawFees \
  --rpc-url $RPC_URL \
  --broadcast
```

**Output**:
```
========================================
FEE WITHDRAWAL
========================================
Factory Fees: 50000000 USDC
Market Fees: 25000000 USDC
Total Withdrawn: 75000000 USDC
Markets Processed: 10
Failed Withdrawals: 0

✅ ALL FEES WITHDRAWN SUCCESSFULLY
```

---

### EmergencyPause.s.sol

**Purpose**: Emergency pause all markets in case of security issue.

**⚠️ EMERGENCY USE ONLY**

**Usage**:
```bash
# Pause all markets immediately
forge script script/EmergencyPause.s.sol:EmergencyPause \
  --rpc-url $RPC_URL \
  --broadcast

# Document the reason for emergency pause!
```

**What it does**:
- Pauses all active markets
- Prevents all trading
- Allows time to investigate and fix security issues

**Next Steps After Pause**:
1. Identify and document the issue
2. Develop and test fix
3. Re-audit if necessary
4. Communicate with users
5. Use `EmergencyUnpause.s.sol` when ready

---

### EmergencyUnpause.s.sol

**Purpose**: Resume operations after emergency is resolved.

**⚠️ Only use after confirming issue is fixed!**

**Pre-Unpause Checklist**:
- [ ] Security issue identified and fixed
- [ ] Contracts re-audited if needed
- [ ] Stakeholders notified
- [ ] Fix tested on testnet
- [ ] Post-mortem documented

**Usage**:
```bash
forge script script/EmergencyUnpause.s.sol:EmergencyUnpause \
  --rpc-url $RPC_URL \
  --broadcast
```

---

## 🔧 Environment Variables

Required `.env` configuration:

```bash
# Deployer/Owner wallet
PRIVATE_KEY=0x...

# Network RPCs
BASE_SEPOLIA_RPC=https://sepolia.base.org
BASE_MAINNET_RPC=https://mainnet.base.org

# Contract verification
BASESCAN_API_KEY=your_api_key

# Deployed addresses (set after deployment)
FACTORY_ADDRESS=0x...
USDC_ADDRESS=0x...

# Fee collection
FEE_RECIPIENT=0x...
```

---

## 📊 Monitoring Setup

### Daily Monitoring (Automated)

```bash
# Add to crontab: crontab -e
# Run health check every 6 hours
0 */6 * * * cd /path/to/truthy-contracts && \
  forge script script/MonitorHealth.s.sol:MonitorHealth \
  --rpc-url $BASE_SEPOLIA_RPC > /tmp/health-$(date +\%Y\%m\%d-\%H\%M).log

# Check for expired markets daily at 9 AM
0 9 * * * cd /path/to/truthy-contracts && \
  forge script script/BatchResolve.s.sol:BatchResolve \
  --rpc-url $BASE_SEPOLIA_RPC > /tmp/expired-$(date +\%Y\%m\%d).log
```

### Weekly Tasks

```bash
# Every Monday at 10 AM: Withdraw fees
0 10 * * 1 cd /path/to/truthy-contracts && \
  forge script script/WithdrawFees.s.sol:WithdrawFees \
  --rpc-url $BASE_SEPOLIA_RPC \
  --broadcast > /tmp/fees-$(date +\%Y\%m\%d).log
```

---

## 🐛 Troubleshooting

### Script Fails with "FACTORY_ADDRESS not set"

```bash
# Ensure .env has correct addresses
echo "FACTORY_ADDRESS=0x..." >> .env
echo "USDC_ADDRESS=0x..." >> .env

# Load environment
source .env
```

### "Insufficient funds for gas"

```bash
# Check balance
cast balance $YOUR_ADDRESS --rpc-url $RPC_URL

# For testnet, get ETH from faucet:
# https://www.coinbase.com/faucets/base-ethereum-goerli-faucet
```

### "Only owner can call this function"

```bash
# Verify you're using the owner's private key
# Check current owner:
cast call $FACTORY_ADDRESS "owner()" --rpc-url $RPC_URL

# Ensure PRIVATE_KEY matches owner
```

### Script shows "Unknown error"

```bash
# Run with maximum verbosity for details
forge script script/YourScript.s.sol:YourScript \
  --rpc-url $RPC_URL \
  -vvvvv
```

---

## 📚 Additional Resources

- [Deployment Runbook](../DEPLOYMENT_RUNBOOK.md) - Complete deployment guide
- [Launch Guide](../LAUNCH_GUIDE.md) - Production launch checklist
- [Security Audit](../SECURITY_AUDIT.md) - Security review
- [Gas Optimizations](../GAS_OPTIMIZATIONS.md) - Gas efficiency guide

---

## 🆘 Emergency Contacts

If you encounter critical issues:

1. **Pause markets immediately**: Use `EmergencyPause.s.sol`
2. **Contact security team**: [security-email]
3. **Post in Discord**: [discord-link]
4. **Submit issue**: [github-issues]

---

## ✅ Script Checklist for Production

Before mainnet deployment, test all scripts:

- [ ] `Deploy.s.sol` - Deploy successful
- [ ] `PostDeploymentCheck.s.sol` - All checks pass
- [ ] `CreateDemoMarket.s.sol` - Markets created
- [ ] `TestTrading.s.sol` - Trading works
- [ ] `MonitorHealth.s.sol` - Health data displays
- [ ] `BatchResolve.s.sol` - Resolution works
- [ ] `WithdrawFees.s.sol` - Fees withdraw
- [ ] `EmergencyPause.s.sol` - Pause works
- [ ] `EmergencyUnpause.s.sol` - Unpause works

---

**Last Updated**: 2025-11-14
**Ready for Production**: ✅
