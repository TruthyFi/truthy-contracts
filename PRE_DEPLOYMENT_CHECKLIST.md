# Pre-Deployment Checklist

**Complete this checklist before deploying to mainnet.**

## 📋 Code Quality

- [ ] All tests passing: `forge test`
- [ ] Test coverage >90%: `forge coverage`
- [ ] No compiler warnings: `forge build`
- [ ] Code formatted: `forge fmt`
- [ ] Gas snapshots updated: `forge snapshot`
- [ ] No TODO comments in production code
- [ ] All magic numbers replaced with constants
- [ ] All functions have NatSpec documentation

## 🔒 Security

- [ ] External audit completed (Required for mainnet)
- [ ] Bug bounty program set up
- [ ] Slither analysis run: `slither .`
- [ ] Access control reviewed
- [ ] Reentrancy protection verified
- [ ] Integer overflow checks confirmed (Solidity 0.8+)
- [ ] All external calls use SafeERC20
- [ ] Emergency pause mechanism tested
- [ ] Multi-sig wallet configured for owner
- [ ] Private keys secured in hardware wallet

## 🧪 Testing

- [ ] Unit tests: `forge test --match-path tests/unit/`
- [ ] Integration tests: `forge test --match-path tests/integration/`
- [ ] Fuzz tests (10k runs): `forge test --match-path tests/fuzz/ --fuzz-runs 10000`
- [ ] Testnet deployment successful
- [ ] Testnet trading tested
- [ ] Market creation tested
- [ ] Market resolution tested
- [ ] Fee withdrawal tested
- [ ] Pause/unpause tested
- [ ] Edge cases verified

## 🌐 Deployment Configuration

### Environment Variables

- [ ] `PRIVATE_KEY` set (use hardware wallet for mainnet)
- [ ] `BASESCAN_API_KEY` set for verification
- [ ] `RPC_URL` configured for Base Mainnet
- [ ] Double-check chain ID (Base Mainnet: 8453)

### Contract Parameters

- [ ] Creation fee set appropriately (default: 5 USDC)
- [ ] Protocol fee rate confirmed (default: 2%)
- [ ] Min/max bet limits configured
- [ ] USDC address correct for Base Mainnet: `0x833589fCD6eDb6E08f4c7C32D4f71b54bdA02913`

## 📝 Documentation

- [ ] README.md updated with mainnet addresses
- [ ] Deployment guide complete
- [ ] User documentation ready
- [ ] API documentation (if applicable)
- [ ] Contract addresses documented
- [ ] Basescan verification complete

## 💰 Financial

- [ ] Deployer wallet funded with ETH for gas (~0.1 ETH)
- [ ] Initial liquidity available if needed
- [ ] Fee collection wallet configured
- [ ] Multi-sig signers confirmed
- [ ] Insurance coverage considered (Nexus Mutual)

## 🚀 Deployment Process

### Step 1: Final Tests

```bash
# Run full test suite
forge test -vvv

# Check coverage
forge coverage

# Generate gas report
forge test --gas-report

# Update snapshots
forge snapshot
```

### Step 2: Deploy to Mainnet

```bash
# Deploy contracts
forge script script/Deploy.s.sol:DeployScript \
  --rpc-url $BASE_MAINNET_RPC \
  --broadcast \
  --verify \
  --slow \
  -vvvv

# IMPORTANT: Save deployment addresses!
```

### Step 3: Verify Deployment

```bash
# Set environment variables
export FACTORY_ADDRESS=<deployed_factory_address>
export USDC_ADDRESS=0x833589fCD6eDb6E08f4c7C32D4f71b54bdA02913

# Verify deployment
forge script script/VerifyDeployment.s.sol:VerifyDeployment \
  --rpc-url $BASE_MAINNET_RPC
```

### Step 4: Post-Deployment

- [ ] Contracts verified on Basescan
- [ ] Ownership transferred to multi-sig
- [ ] Initial markets created (if applicable)
- [ ] Frontend updated with new addresses
- [ ] Announce deployment on social media
- [ ] Monitor for first 24 hours

## 🔍 Verification

### On Basescan

- [ ] Source code verified
- [ ] Read functions work
- [ ] Write functions accessible
- [ ] Events emitting correctly
- [ ] Proxy setup correct (if using proxy pattern)

### Functional Tests

- [ ] Create test market with small liquidity
- [ ] Buy small amount of outcome tokens
- [ ] Sell tokens back
- [ ] Verify fees collected
- [ ] Test pause/unpause
- [ ] Resolve test market
- [ ] Claim winnings

## 🚨 Emergency Procedures

### If Issues Found

1. **Minor Issues**
   - Pause affected contracts
   - Assess impact
   - Prepare fix
   - Communicate to users

2. **Critical Issues**
   - Immediately pause all contracts
   - Alert all team members
   - Contact auditors
   - Prepare emergency response

### Contact Information

- [ ] Emergency contact list prepared
- [ ] Auditor contact saved
- [ ] Team communication channel active
- [ ] Community communication plan ready

## 📊 Monitoring

### Post-Deployment Monitoring

- [ ] Tenderly alerts configured
- [ ] OpenZeppelin Defender set up
- [ ] Custom monitoring dashboard
- [ ] Gas price alerts
- [ ] Transaction monitoring
- [ ] Error tracking

### Metrics to Track

- [ ] Total markets created
- [ ] Total volume
- [ ] Active users
- [ ] Fees collected
- [ ] Gas costs
- [ ] Failed transactions
- [ ] Contract balance

## 🎯 Success Criteria

Deployment is successful when:

- [ ] All contracts deployed and verified
- [ ] Ownership transferred to multi-sig
- [ ] At least 3 markets created successfully
- [ ] At least 10 trades executed successfully
- [ ] No critical issues in first 24 hours
- [ ] All monitoring systems operational
- [ ] Frontend connected and functional

## 📞 Support

### If You Need Help

- **Foundry Issues**: https://book.getfoundry.sh/
- **Base Docs**: https://docs.base.org
- **Security**: Contact auditors immediately
- **Community**: Discord/Telegram support

## 🔐 Security Reminders

**DO NOT**:
- ❌ Use hot wallets for mainnet deployment
- ❌ Commit private keys to git
- ❌ Share deployment keys
- ❌ Deploy without audit on mainnet
- ❌ Rush deployment under pressure

**DO**:
- ✅ Use hardware wallet
- ✅ Test on testnet first
- ✅ Have multiple people review
- ✅ Set up monitoring before deploy
- ✅ Keep emergency contacts ready

---

## ✅ Final Sign-Off

**I confirm that:**

- [ ] All items in this checklist are complete
- [ ] External audit has been completed
- [ ] Bug bounty program is active
- [ ] Multi-sig is configured with trusted signers
- [ ] Emergency procedures are documented
- [ ] Team is ready for deployment
- [ ] Monitoring is in place
- [ ] I understand the risks

**Signed**: _________________
**Date**: _________________
**Deployment Lead**: _________________

---

**Note**: This is a critical checklist for mainnet deployment. Do not skip any items. For testnet deployment, you can skip the audit and insurance items, but all other items should be completed.
