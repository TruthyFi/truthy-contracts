# 🚀 Quick Deploy - 15 Minutes, $0 Cost

**Get TruthyFi live on the internet in 15 minutes for FREE!**

---

## ⚡ Step 1: Get Testnet ETH (2 minutes)

Visit: https://www.coinbase.com/faucets/base-ethereum-goerli-faucet

- Enter your wallet address
- Receive 0.1 ETH instantly (FREE)

---

## ⚡ Step 2: Deploy Contracts (3 minutes)

```bash
# Set your private key
export PRIVATE_KEY=your_private_key_here

# Deploy to Base Sepolia (FREE)
forge script script/Deploy.s.sol:DeployScript \
  --rpc-url https://sepolia.base.org \
  --broadcast \
  --verify

# Save these addresses:
# Factory: 0x...
# USDC: 0x...
```

---

## ⚡ Step 3: Create Markets (2 minutes)

```bash
export FACTORY_ADDRESS=0x...  # from step 2
export USDC_ADDRESS=0x...     # from step 2

# Create 5 demo markets
forge script script/CreateDemoMarket.s.sol:CreateDemoMarket \
  --rpc-url https://sepolia.base.org \
  --broadcast
```

---

## ⚡ Step 4: Deploy Frontend (5 minutes)

```bash
cd frontend

# Update addresses in src/config/contracts.ts
# Add your FACTORY_ADDRESS and USDC_ADDRESS for chain 84532

# Install Vercel CLI
npm i -g vercel

# Deploy (creates free account if needed)
vercel --prod

# Your live URL: https://your-app.vercel.app
```

---

## ⚡ Step 5: Test! (3 minutes)

1. Visit your Vercel URL
2. Connect MetaMask (Base Sepolia network)
3. Get test USDC from contract faucet
4. Trade on markets!

---

## 🎉 Done!

**You now have:**
- ✅ Live smart contracts on Base Sepolia
- ✅ Public frontend (Vercel)
- ✅ Shareable demo URL
- ✅ Working prediction markets

**Total Cost: $0.00**
**Total Time: ~15 minutes**

---

## 📋 Share Your Demo

Send this to testers:

```
🌐 Live Demo: https://your-app.vercel.app

📝 How to test:
1. Install MetaMask
2. Add Base Sepolia network
3. Get test ETH: https://www.coinbase.com/faucets/base-ethereum-goerli-faucet
4. Connect wallet to app
5. Get test USDC (call faucet)
6. Start trading!

💡 Everything is on testnet - no real money!
```

---

## 🐛 Troubleshooting

**Deployment failed?**
```bash
# Run verification
forge script script/PostDeploymentCheck.s.sol:PostDeploymentCheck \
  --rpc-url https://sepolia.base.org
```

**Frontend not connecting?**
- Check addresses in `frontend/src/config/contracts.ts`
- Make sure you're on Base Sepolia in MetaMask

**Need more testnet ETH?**
- Visit faucet again (can claim daily)
- Try alternative: https://faucet.quicknode.com/base/sepolia

---

## 📚 Full Guides

For detailed instructions:
- [FREE_DEPLOYMENT.md](./FREE_DEPLOYMENT.md) - Complete guide
- [LOCAL_TESTING_GUIDE.md](./LOCAL_TESTING_GUIDE.md) - Local testing
- [DEPLOYMENT_RUNBOOK.md](./DEPLOYMENT_RUNBOOK.md) - Production

---

**Questions?** Check [FREE_DEPLOYMENT.md](./FREE_DEPLOYMENT.md) for detailed help!
