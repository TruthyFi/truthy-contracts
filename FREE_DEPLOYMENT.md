# Free Deployment Guide

Complete guide to deploy TruthyFi for **$0.00** for testing and demos.

---

## 🆓 Total Cost: FREE

- Smart Contracts: FREE (Base Sepolia testnet)
- Frontend: FREE (Vercel/Netlify)
- Domain: FREE (.vercel.app subdomain)
- SSL: FREE (automatic)
- Bandwidth: FREE (generous limits)

---

## Part 1: Deploy Smart Contracts (FREE)

### Step 1: Get FREE Testnet ETH

Visit one of these faucets:

1. **Coinbase Base Faucet** (Best)
   - URL: https://www.coinbase.com/faucets/base-ethereum-goerli-faucet
   - Gives: 0.1 ETH per day
   - Requirements: Coinbase account (free)

2. **QuickNode Faucet** (Alternative)
   - URL: https://faucet.quicknode.com/base/sepolia
   - Gives: 0.05 ETH
   - Requirements: Twitter account

3. **Alchemy Faucet** (Alternative)
   - URL: https://www.alchemy.com/faucets/base-sepolia
   - Gives: 0.1 ETH
   - Requirements: Alchemy account (free)

**Enter your wallet address and receive FREE testnet ETH instantly!**

### Step 2: Deploy Contracts

```bash
# Create .env file
cat > .env << 'EOF'
PRIVATE_KEY=your_private_key_here
BASE_SEPOLIA_RPC=https://sepolia.base.org
BASESCAN_API_KEY=  # Optional for verification
EOF

# Deploy to Base Sepolia (FREE - uses testnet ETH)
forge script script/Deploy.s.sol:DeployScript \
  --rpc-url https://sepolia.base.org \
  --broadcast \
  --verify

# Save the addresses from output
export FACTORY_ADDRESS=0x...
export USDC_ADDRESS=0x...
```

**Cost: $0.00** (testnet ETH is free)

### Step 3: Verify Deployment

```bash
# Run comprehensive checks (free)
forge script script/PostDeploymentCheck.s.sol:PostDeploymentCheck \
  --rpc-url https://sepolia.base.org

# Should show: "✅ ALL CHECKS PASSED"
```

### Step 4: Create Demo Markets

```bash
# Create 5 demo markets (free)
forge script script/CreateDemoMarket.s.sol:CreateDemoMarket \
  --rpc-url https://sepolia.base.org \
  --broadcast

# View on BaseScan
echo "View your contracts:"
echo "Factory: https://sepolia.basescan.org/address/$FACTORY_ADDRESS"
echo "USDC: https://sepolia.basescan.org/address/$USDC_ADDRESS"
```

**✅ Contracts deployed publicly for FREE!**

---

## Part 2: Deploy Frontend (FREE)

### Option 1: Vercel (Recommended)

**Why Vercel?**
- ✅ FREE forever plan
- ✅ Automatic deployments from Git
- ✅ Global CDN
- ✅ SSL included
- ✅ Environment variables
- ✅ Preview deployments for PRs

**Setup:**

```bash
cd frontend

# 1. Install Vercel CLI
npm i -g vercel

# 2. Update contract addresses in src/config/contracts.ts
# Edit the file to add your Base Sepolia addresses:
export const CONTRACTS = {
  84532: { // Base Sepolia
    factory: '0x...', // Your deployed factory
    usdc: '0x...',    // Your deployed USDC
  },
}

# 3. Login to Vercel (creates free account)
vercel login

# 4. Deploy!
vercel

# Follow the prompts:
# - Link to Git? (optional, recommended)
# - Project name: truthy-fi
# - Deploy!

# 5. Production deployment
vercel --prod
```

**Result:**
- Live URL: `https://truthy-fi.vercel.app`
- Updates automatically when you push to Git
- **Cost: $0/month**

**Vercel Free Tier Includes:**
- Unlimited websites
- 100GB bandwidth/month
- Serverless functions
- Automatic SSL
- Custom domains (bring your own)

### Option 2: Netlify

```bash
cd frontend

# 1. Install Netlify CLI
npm i -g netlify-cli

# 2. Build
npm run build

# 3. Login (creates free account)
netlify login

# 4. Deploy
netlify deploy

# 5. Production deployment
netlify deploy --prod
```

**Result:**
- Live URL: `https://truthy-fi.netlify.app`
- **Cost: $0/month**

**Netlify Free Tier:**
- 100GB bandwidth/month
- 300 build minutes/month
- Automatic SSL
- Form handling
- Serverless functions

### Option 3: Cloudflare Pages

```bash
cd frontend

# 1. Build
npm run build

# 2. Install Wrangler
npm i -g wrangler

# 3. Login
wrangler login

# 4. Deploy
wrangler pages publish out
```

**Cloudflare Free Tier:**
- Unlimited bandwidth
- Unlimited requests
- 500 builds/month

---

## Part 3: Complete Free Stack

After deployment, you'll have:

```
┌─────────────────────────────────┐
│  Frontend (Vercel - FREE)       │
│  https://truthy-fi.vercel.app   │
└────────────┬────────────────────┘
             │
             ↓
┌─────────────────────────────────┐
│  Smart Contracts (Base Sepolia) │
│  Factory: 0x...                 │
│  USDC: 0x...                    │
│  (FREE - testnet)               │
└─────────────────────────────────┘
```

**Total Monthly Cost: $0.00**

---

## Testing Your Deployment

### 1. View Contracts on BaseScan

Visit your deployed contracts:
```
Factory: https://sepolia.basescan.org/address/YOUR_FACTORY_ADDRESS
```

You can see:
- Contract code (verified)
- All transactions
- Events emitted
- Market creation
- Trades

### 2. Test Frontend

Visit your deployed site:
```
https://truthy-fi.vercel.app
```

**Connect MetaMask:**
1. Switch to Base Sepolia network
2. Get test USDC from faucet (in contract)
3. Browse markets
4. Make trades!

### 3. Get Test USDC

Your deployed MockUSDC has a faucet:

```bash
# Get 1000 test USDC (free)
cast send $USDC_ADDRESS \
  "faucet()" \
  --rpc-url https://sepolia.base.org \
  --private-key $PRIVATE_KEY

# Or call from frontend - connect wallet and call faucet()
```

---

## Sharing Your Deployment

Share these links with testers:

**Frontend:**
```
🌐 Live Demo: https://truthy-fi.vercel.app
```

**Smart Contracts:**
```
📝 Factory: https://sepolia.basescan.org/address/YOUR_FACTORY
📊 View Markets
💰 All trades visible on-chain
```

**Instructions for Testers:**
1. Visit the frontend URL
2. Install MetaMask (if needed)
3. Add Base Sepolia network
4. Get test ETH from faucet: https://www.coinbase.com/faucets/base-ethereum-goerli-faucet
5. Connect wallet
6. Get test USDC (call faucet in contract)
7. Start trading!

---

## Free CI/CD (Bonus)

### Vercel Auto-Deploy from Git

1. **Connect Vercel to GitHub:**
   ```bash
   # During vercel setup, link to your repo
   vercel --prod
   # Select: Link to Git repository
   ```

2. **Every push to main = auto-deploy!**
   - Push to GitHub
   - Vercel builds automatically
   - Live in ~2 minutes
   - Preview deployments for PRs

**Cost: FREE**

### GitHub Actions (Already set up!)

Your repo has CI/CD in `.github/workflows/ci.yml`:
- ✅ Runs on every push (free)
- ✅ Tests all contracts
- ✅ Coverage reports
- ✅ Gas snapshots
- ✅ Security analysis

**GitHub Actions Free Tier:**
- 2,000 minutes/month (plenty)
- Unlimited for public repos

---

## Free Monitoring

### 1. BaseScan (Free)

View all activity on your contracts:
- Market creation events
- Trades
- Resolutions
- Fee collection

**Cost: FREE**

### 2. Dune Analytics (Free)

Create dashboards for your deployment:
- Total volume
- Active markets
- User analytics

**Cost: FREE** (basic dashboards)

### 3. Tenderly (Free Tier)

Monitor transactions and debug:
- Transaction simulations
- Gas profiling
- Alerts

**Cost: FREE** (limited features)

---

## Upgrade Costs (Optional)

If you want to upgrade later (not needed for testing):

### Vercel Pro
- $20/month
- More bandwidth
- Better analytics
- Team features

### Custom Domain
- $10-15/year
- truthyfi.xyz
- Buy from Namecheap, Google Domains, etc.

### Mainnet Deployment
- ~$30 in ETH for gas (one-time)
- Uses real USDC

---

## Free Alternative Testnets

If you want to try other networks (all FREE):

### Optimism Sepolia
```bash
# Get free OP Sepolia ETH
# Faucet: https://app.optimism.io/faucet

forge script script/Deploy.s.sol:DeployScript \
  --rpc-url https://sepolia.optimism.io \
  --broadcast
```

### Arbitrum Sepolia
```bash
# Faucet: https://faucet.quicknode.com/arbitrum/sepolia

forge script script/Deploy.s.sol:DeployScript \
  --rpc-url https://sepolia.arbitrum.io \
  --broadcast
```

### Polygon Mumbai (being deprecated)
```bash
# Faucet: https://faucet.polygon.technology/

forge script script/Deploy.s.sol:DeployScript \
  --rpc-url https://rpc-mumbai.maticvigil.com \
  --broadcast
```

**All testnets are FREE!**

---

## Common Questions

### Q: How long is it free?

**A: Forever!** Testnet ETH is always free, and Vercel's free tier has no time limit.

### Q: What are the limits?

**Vercel Free Tier:**
- 100GB bandwidth/month (enough for 10,000+ visits)
- 100 serverless function hours
- 6,000 build minutes/year

For a testing/demo app, you'll never hit these limits.

### Q: Can I use a custom domain?

**A:** Yes! Vercel allows custom domains on free tier:
```bash
# Add domain in Vercel dashboard
# Point DNS to Vercel
# SSL added automatically
```

Domain costs ~$10/year (from Namecheap, etc.)

### Q: How do I update the deployment?

**Option 1: Auto-deploy from Git**
```bash
# Just push to GitHub
git add .
git commit -m "Update"
git push

# Vercel auto-deploys in ~2 minutes
```

**Option 2: Manual deploy**
```bash
cd frontend
vercel --prod
```

### Q: Can testers use real money?

**A:** No! Base Sepolia uses testnet ETH and MockUSDC. No real money involved. Perfect for testing!

### Q: What if I run out of testnet ETH?

**A:** Just visit the faucet again! Most faucets let you get more every 24 hours.

---

## Quick Deploy Checklist

- [ ] Get testnet ETH from faucet (5 min)
- [ ] Deploy contracts to Base Sepolia (2 min)
- [ ] Verify deployment (1 min)
- [ ] Create demo markets (1 min)
- [ ] Update frontend config with addresses (1 min)
- [ ] Deploy frontend to Vercel (3 min)
- [ ] Test trading (2 min)
- [ ] Share with testers! 🎉

**Total Time: ~15 minutes**
**Total Cost: $0.00**

---

## Support

Having issues with free deployment?

1. **Faucet not working?** Try alternative faucets listed above
2. **Vercel issues?** Check [Vercel docs](https://vercel.com/docs)
3. **Contract issues?** Run `forge script script/PostDeploymentCheck.s.sol`

---

**You can run a fully functional prediction market platform for FREE! 🎉**

Perfect for:
- Testing with real users
- Gathering feedback
- Showing to investors
- Applying for grants
- Building portfolio
- Proving concept

No credit card required. No hidden costs. 100% free for testing!
