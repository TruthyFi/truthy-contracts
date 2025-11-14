# TruthyFi Deployment Runbook

**Version**: 1.0.0
**Last Updated**: 2025-11-14
**Target Networks**: Base Sepolia (Testnet), Base Mainnet

---

## 📋 Table of Contents

1. [Prerequisites](#prerequisites)
2. [Pre-Deployment Checklist](#pre-deployment-checklist)
3. [Deployment Steps](#deployment-steps)
4. [Post-Deployment Verification](#post-deployment-verification)
5. [Emergency Procedures](#emergency-procedures)
6. [Monitoring & Maintenance](#monitoring--maintenance)
7. [Troubleshooting](#troubleshooting)

---

## Prerequisites

### Required Software

- [Foundry](https://book.getfoundry.sh/getting-started/installation) (latest)
- Node.js v18+ (for frontend)
- Git
- Make (optional)

### Environment Setup

Create a `.env` file in the project root:

```bash
# Deployer wallet
PRIVATE_KEY=your_private_key_here

# RPC URLs
BASE_SEPOLIA_RPC=https://sepolia.base.org
BASE_MAINNET_RPC=https://mainnet.base.org

# Etherscan API (for contract verification)
BASESCAN_API_KEY=your_basescan_api_key

# Deployment addresses (set after deployment)
FACTORY_ADDRESS=
USDC_ADDRESS=

# Fee recipient
FEE_RECIPIENT=your_fee_recipient_address
```

### Funding Requirements

**Base Sepolia (Testnet)**:
- 0.1 ETH for deployment gas
- Get from: https://www.coinbase.com/faucets/base-ethereum-goerli-faucet

**Base Mainnet**:
- ~0.05 ETH for deployment
- Varies based on gas prices

---

## Pre-Deployment Checklist

Run through this checklist before deploying:

### Code Quality ✅

```bash
# 1. Run all tests
forge test

# 2. Check test coverage (should be >90%)
forge coverage

# 3. Run gas report
forge test --gas-report

# 4. Check code formatting
forge fmt --check

# 5. Build contracts
forge build

# 6. Generate gas snapshot
forge snapshot
```

### Security ✅

```bash
# 7. Run security analysis (if Slither installed)
slither . --foundry-out-directory out --exclude-dependencies

# 8. Review SECURITY_AUDIT.md
cat SECURITY_AUDIT.md

# 9. Verify no high/critical vulnerabilities
# All findings should be documented and mitigated
```

### Configuration ✅

- [ ] Review creation fee (default: 5 USDC)
- [ ] Review protocol fee rate (default: 2%)
- [ ] Verify USDC address for network
  - Base Sepolia: Deploy MockUSDC (auto-handled)
  - Base Mainnet: `0x833589fCD6eDb6E08f4c7C32D4f71b54bdA02913`
- [ ] Set fee recipient address
- [ ] Backup deployer private key securely

---

## Deployment Steps

### Step 1: Deploy to Base Sepolia (Testnet)

```bash
# Load environment variables
source .env

# Run deployment script
forge script script/Deploy.s.sol:DeployScript \
  --rpc-url $BASE_SEPOLIA_RPC \
  --broadcast \
  --verify \
  -vvvv

# Save deployment addresses
# They will be saved to: deployments/84532.json
```

**Expected Output**:
```
Deploying from: 0x...
Chain ID: 84532
MockUSDC deployed at: 0x...
TruthyMarketFactory deployed at: 0x...
Payment token: 0x...
Creation fee: 5000000
Protocol fee rate: 200
```

**Update .env**:
```bash
FACTORY_ADDRESS=<factory_address_from_output>
USDC_ADDRESS=<usdc_address_from_output>
```

### Step 2: Verify Deployment

```bash
# Run comprehensive verification
forge script script/PostDeploymentCheck.s.sol:PostDeploymentCheck \
  --rpc-url $BASE_SEPOLIA_RPC

# Expected: "✅ ALL CHECKS PASSED - DEPLOYMENT VERIFIED!"
```

### Step 3: Create Demo Markets

```bash
# Create 5 demo markets
forge script script/CreateDemoMarket.s.sol:CreateDemoMarket \
  --rpc-url $BASE_SEPOLIA_RPC \
  --broadcast

# Verify markets were created
forge script script/VerifyDeployment.s.sol:VerifyDeployment \
  --rpc-url $BASE_SEPOLIA_RPC
```

### Step 4: Test Trading

```bash
# Run interactive trading test
forge script script/TestTrading.s.sol:TestTrading \
  --rpc-url $BASE_SEPOLIA_RPC \
  --broadcast

# Expected: "✅ Trading test completed successfully!"
```

### Step 5: Deploy Frontend

```bash
cd frontend

# Install dependencies
npm install

# Update contract addresses in src/config/contracts.ts
# Set FACTORY_ADDRESS and USDC_ADDRESS for Base Sepolia

# Run development server
npm run dev

# Build for production
npm run build

# Deploy to Vercel/Netlify
vercel deploy
# or
netlify deploy
```

### Step 6: Monitor Health

```bash
# Run health monitor
forge script script/MonitorHealth.s.sol:MonitorHealth \
  --rpc-url $BASE_SEPOLIA_RPC

# Set up recurring monitoring (e.g., via cron)
# */30 * * * * cd /path/to/truthy-contracts && forge script script/MonitorHealth.s.sol...
```

---

## Post-Deployment Verification

### Automated Verification

Run the comprehensive post-deployment check:

```bash
forge script script/PostDeploymentCheck.s.sol:PostDeploymentCheck \
  --rpc-url $BASE_SEPOLIA_RPC
```

This checks:
- ✅ Factory configuration
- ✅ USDC integration
- ✅ Market creation
- ✅ Trading functionality
- ✅ Gas optimizations
- ✅ Security features

### Manual Verification

1. **Check on BaseScan**:
   - Factory: https://sepolia.basescan.org/address/FACTORY_ADDRESS
   - Verify contract is verified
   - Check transactions are processing

2. **Test in Frontend**:
   - Connect wallet
   - Browse markets
   - Execute test trade
   - Verify UI updates

3. **Check Prices**:
   - YES + NO should equal ~100%
   - Prices should update after trades
   - Preview costs should match actual

4. **Verify Fees**:
   - Check factory accumulated fees
   - Check market fees
   - Confirm 2% fee rate

---

## Emergency Procedures

### Emergency Pause

If a security issue is discovered:

```bash
# STEP 1: Pause all markets immediately
forge script script/EmergencyPause.s.sol:EmergencyPause \
  --rpc-url $BASE_SEPOLIA_RPC \
  --broadcast

# STEP 2: Assess the situation
# - Identify the vulnerability
# - Determine impact and affected users
# - Plan mitigation strategy

# STEP 3: Communicate
# - Post on Twitter/Discord
# - Email users if possible
# - Update status page

# STEP 4: Fix and audit
# - Deploy fix to testnet
# - Re-audit if necessary
# - Test thoroughly

# STEP 5: Resume after fix confirmed
forge script script/EmergencyUnpause.s.sol:EmergencyUnpause \
  --rpc-url $BASE_SEPOLIA_RPC \
  --broadcast
```

### Emergency Contacts

- **Smart Contract Team**: [your-email]
- **Security Auditor**: [auditor-email]
- **Base Support**: https://discord.gg/buildonbase

---

## Monitoring & Maintenance

### Daily Tasks

```bash
# Check system health
forge script script/MonitorHealth.s.sol:MonitorHealth \
  --rpc-url $BASE_SEPOLIA_RPC

# Check for expired markets needing resolution
forge script script/BatchResolve.s.sol:BatchResolve \
  --rpc-url $BASE_SEPOLIA_RPC
```

### Weekly Tasks

```bash
# Withdraw accumulated fees
forge script script/WithdrawFees.s.sol:WithdrawFees \
  --rpc-url $BASE_SEPOLIA_RPC \
  --broadcast

# Review gas costs and optimize if needed
forge test --gas-report

# Check for contract upgrades/optimizations
forge snapshot --diff
```

### Monthly Tasks

- Review security advisories for dependencies
- Update OpenZeppelin contracts if needed
- Analyze user feedback and feature requests
- Review and optimize gas costs
- Check for new Base ecosystem opportunities

### Metrics to Track

- **Markets**: Total created, active, resolved
- **Volume**: Daily/weekly/monthly trading volume
- **Fees**: Protocol revenue
- **Users**: Unique traders, retention rate
- **Gas**: Average transaction costs
- **Liquidity**: Total locked value

---

## Troubleshooting

### Deployment Failed

**Error**: "Insufficient funds"
```bash
# Check balance
cast balance $YOUR_ADDRESS --rpc-url $BASE_SEPOLIA_RPC

# Get testnet ETH
# Visit: https://www.coinbase.com/faucets/base-ethereum-goerli-faucet
```

**Error**: "Contract verification failed"
```bash
# Manually verify on BaseScan
# 1. Go to: https://sepolia.basescan.org/verifyContract
# 2. Select "Solidity (Single file)"
# 3. Upload flattened contract:
forge flatten src/TruthyMarketFactory.sol > flattened.sol
# 4. Set compiler version: 0.8.20
# 5. Enable optimization: 200 runs
```

### Trading Not Working

**Issue**: "Insufficient allowance"
```bash
# Users need to approve market to spend USDC
# Frontend should handle this automatically
# Manual approval:
cast send $USDC_ADDRESS \
  "approve(address,uint256)" \
  $MARKET_ADDRESS \
  $(cast max-uint256) \
  --rpc-url $BASE_SEPOLIA_RPC \
  --private-key $PRIVATE_KEY
```

**Issue**: "Market paused"
```bash
# Check if market is paused
cast call $MARKET_ADDRESS "paused()" --rpc-url $BASE_SEPOLIA_RPC

# Unpause (owner only)
cast send $MARKET_ADDRESS "unpause()" \
  --rpc-url $BASE_SEPOLIA_RPC \
  --private-key $OWNER_PRIVATE_KEY
```

### High Gas Costs

```bash
# Generate gas report
forge test --gas-report

# Compare with snapshot
forge snapshot --diff

# Review GAS_OPTIMIZATIONS.md for optimization strategies
cat GAS_OPTIMIZATIONS.md
```

### Frontend Not Connecting

1. **Check network**: Ensure wallet is on Base Sepolia
2. **Check RPC**: Verify RPC URL in wagmi config
3. **Check contracts**: Verify addresses in `src/config/contracts.ts`
4. **Check ABIs**: Ensure ABIs are up to date in `src/config/abis.ts`

---

## Deployment to Mainnet

When ready to deploy to Base Mainnet:

### Pre-Mainnet Checklist

- [ ] All testnet testing completed successfully
- [ ] Security audit reviewed and signed off
- [ ] 30+ days of testnet operation with no issues
- [ ] Frontend tested extensively
- [ ] Emergency procedures tested
- [ ] Insurance/bug bounty program in place
- [ ] Legal/compliance review completed
- [ ] User documentation ready
- [ ] Support channels established
- [ ] Sufficient ETH for deployment (~0.05 ETH)

### Mainnet Deployment

```bash
# DOUBLE CHECK: You're deploying to MAINNET
# This costs real money and is permanent

forge script script/Deploy.s.sol:DeployScript \
  --rpc-url $BASE_MAINNET_RPC \
  --broadcast \
  --verify \
  --slow \
  -vvvv

# Verify deployment
forge script script/PostDeploymentCheck.s.sol:PostDeploymentCheck \
  --rpc-url $BASE_MAINNET_RPC

# Update frontend with mainnet addresses
# Deploy frontend to production

# Announce launch! 🚀
```

---

## Additional Resources

- [Base Documentation](https://docs.base.org/)
- [Foundry Book](https://book.getfoundry.sh/)
- [OpenZeppelin Contracts](https://docs.openzeppelin.com/contracts/)
- [TruthyFi Security Audit](./SECURITY_AUDIT.md)
- [Gas Optimizations Guide](./GAS_OPTIMIZATIONS.md)
- [Launch Guide](./LAUNCH_GUIDE.md)

---

## Support

For deployment issues or questions:
- GitHub Issues: [your-repo-url]
- Discord: [your-discord]
- Email: [support-email]

---

**Last Review**: 2025-11-14
**Next Review**: Before mainnet deployment

✅ **Ready for Testnet Deployment**
