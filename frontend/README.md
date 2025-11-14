# TruthyFi Frontend

> Social prediction markets powered by Base - Put your money where your mouth is

## 🚀 Overview

The TruthyFi frontend is a Next.js 14 application that provides a beautiful, responsive interface for interacting with TruthyFi's social prediction markets on Base.

**Key Features:**
- 🎨 Modern, responsive UI with Tailwind CSS
- 🔗 Seamless wallet connection with RainbowKit
- ⚡ Real-time market data with wagmi hooks
- 📊 Interactive trading interface
- 🎭 Farcaster Frame integration
- 📱 Mobile-first design

## 📋 Tech Stack

- **Framework**: Next.js 14 (App Router)
- **Language**: TypeScript
- **Styling**: Tailwind CSS
- **Web3**: wagmi v2 + viem v2
- **Wallet**: RainbowKit v2
- **State Management**: TanStack Query
- **Icons**: Lucide React
- **Blockchain**: Base (Sepolia testnet, Mainnet ready)

## 🛠 Prerequisites

- Node.js 18+ and npm/yarn/pnpm
- Wallet with Base Sepolia ETH for testing
- WalletConnect Project ID ([get one free](https://cloud.walletconnect.com))

## 📦 Installation

```bash
# Navigate to frontend directory
cd frontend

# Install dependencies
npm install
# or
yarn install
# or
pnpm install
```

## ⚙️ Configuration

1. **Copy environment template:**
```bash
cp .env.example .env.local
```

2. **Configure environment variables:**
```env
# Required: Get from https://cloud.walletconnect.com
NEXT_PUBLIC_WALLETCONNECT_PROJECT_ID=your_project_id_here

# Required: Add deployed contract addresses
NEXT_PUBLIC_FACTORY_ADDRESS_SEPOLIA=0x...
NEXT_PUBLIC_USDC_ADDRESS_SEPOLIA=0x...

# For production (Base Mainnet)
NEXT_PUBLIC_FACTORY_ADDRESS_MAINNET=0x...
NEXT_PUBLIC_USDC_ADDRESS_MAINNET=0x833589fCD6eDb6E08f4c7C32D4f71b54bdA02913

# App URL (for Farcaster Frames)
NEXT_PUBLIC_URL=http://localhost:3000
```

3. **Get contract addresses:**
   - Deploy contracts using `forge script` (see main README)
   - Copy addresses from deployment output
   - Or use existing deployed addresses on Base Sepolia

## 🏃‍♂️ Running the App

### Development Mode

```bash
npm run dev
```

Open [http://localhost:3000](http://localhost:3000)

### Production Build

```bash
npm run build
npm start
```

### Lint

```bash
npm run lint
```

## 📁 Project Structure

```
frontend/
├── src/
│   ├── app/                    # Next.js App Router pages
│   │   ├── layout.tsx          # Root layout with providers
│   │   ├── page.tsx            # Home page (market discovery)
│   │   ├── market/[address]/   # Market detail pages
│   │   ├── create/             # Create market page
│   │   ├── profile/            # User profile page
│   │   └── api/                # API routes (Farcaster Frames)
│   ├── components/             # React components
│   │   ├── layout/             # Layout components (Header, Footer)
│   │   ├── markets/            # Market-related components
│   │   ├── trading/            # Trading interface
│   │   ├── filters/            # Search & filter components
│   │   └── stats/              # Statistics components
│   ├── config/                 # Configuration files
│   │   ├── contracts.ts        # Contract addresses & constants
│   │   ├── abis.ts             # Contract ABIs
│   │   └── wagmi.ts            # Wagmi configuration
│   ├── lib/                    # Utility functions
│   │   └── utils.ts            # Helper functions
│   └── providers/              # React context providers
│       └── Web3Provider.tsx    # Web3 provider wrapper
├── public/                     # Static assets
├── package.json                # Dependencies
├── tsconfig.json               # TypeScript config
├── tailwind.config.ts          # Tailwind config
└── next.config.mjs             # Next.js config
```

## 🎯 Key Features

### 1. Market Discovery
- Browse all available markets
- Filter by category (crypto, politics, sports, etc.)
- Search markets by name
- View real-time odds and statistics

### 2. Trading Interface
- Buy YES or NO outcome tokens
- See real-time price updates
- Automatic USDC approval flow
- Transaction confirmation feedback
- Min/max bet enforcement

### 3. Market Details
- Comprehensive market information
- Current odds visualization
- Historical volume and liquidity
- Link to source (Twitter/Farcaster post)
- Creator and resolver information

### 4. User Profile (Coming Soon)
- Betting history
- Win rate statistics
- Total volume traded
- Active positions

### 5. Create Market (Coming Soon)
- Simple market creation form
- Category selection
- Initial liquidity configuration
- Link to social post

### 6. Farcaster Frames
- Bet directly from Farcaster feed
- Share markets virally
- In-feed transaction signing

## 🔌 Contract Integration

The frontend interacts with three main contracts:

### TruthyMarketFactory
- **Purpose**: Create and retrieve markets
- **Key Functions**:
  - `getAllMarkets()` - Get all market addresses
  - `getMarketsByCategory()` - Filter by category
  - `createMarket()` - Deploy new market

### TruthyMarket
- **Purpose**: Individual prediction market
- **Key Functions**:
  - `buyOutcome()` - Purchase YES/NO tokens
  - `redeemOutcome()` - Sell or claim winnings
  - `getOutcomePrice()` - Get current odds
  - `previewCostToBuy()` - Estimate trade cost

### USDC (ERC20)
- **Purpose**: Payment token
- **Key Functions**:
  - `approve()` - Allow market to spend USDC
  - `balanceOf()` - Check user balance
  - `faucet()` - Get test USDC (testnet only)

## 🎨 Customization

### Theming

Colors are defined in `tailwind.config.ts`:

```typescript
colors: {
  yes: { light: '#86efac', DEFAULT: '#22c55e', dark: '#16a34a' },
  no: { light: '#fca5a5', DEFAULT: '#ef4444', dark: '#dc2626' },
  // ... more colors
}
```

### Categories

Add/edit categories in `src/config/contracts.ts`:

```typescript
export const CATEGORIES = [
  'crypto',
  'politics',
  'sports',
  // ... add more
] as const;
```

## 🐛 Troubleshooting

### Common Issues

**1. "Cannot connect wallet"**
- Check WalletConnect Project ID is set
- Ensure you're on Base Sepolia network
- Try clearing browser cache

**2. "Contract not found"**
- Verify contract addresses in `.env.local`
- Ensure contracts are deployed to Base Sepolia
- Check you're connected to correct network

**3. "Insufficient balance"**
- Get test ETH from [Base faucet](https://www.coinbase.com/faucets/base-ethereum-goerli-faucet)
- Call `faucet()` on MockUSDC contract for test USDC
- Check you have enough for gas + trade

**4. "Transaction failed"**
- Check USDC approval first
- Ensure bet amount is within limits ($0.50 - $1,000)
- Verify market hasn't expired

## 🚢 Deployment

### Vercel (Recommended)

1. Push code to GitHub
2. Import repo in Vercel
3. Add environment variables
4. Deploy

```bash
# Or use Vercel CLI
npm i -g vercel
vercel
```

### Other Platforms

Works on any platform supporting Next.js:
- Netlify
- Railway
- AWS Amplify
- Docker

## 📱 Farcaster Integration

### Frame Setup

Frames allow users to bet directly from Farcaster:

1. **Create frame endpoint**: `/api/frames/[marketId]/route.ts`
2. **Add frame metadata**: Meta tags for frame protocol
3. **Handle transactions**: Sign transactions in-feed
4. **Test on Warpcast**: Share frame URL

**Example Frame:**
```typescript
// See src/app/api/frames/[marketId]/route.ts
```

## 🧪 Testing

### Manual Testing Checklist

- [ ] Connect wallet (MetaMask, Coinbase Wallet, WalletConnect)
- [ ] View market list
- [ ] Filter by category
- [ ] Search markets
- [ ] Open market detail
- [ ] Approve USDC
- [ ] Buy YES outcome
- [ ] Buy NO outcome
- [ ] Check balance updates
- [ ] View transaction on Basescan

### Test with MockUSDC

```typescript
// Call faucet to get 1000 test USDC
const { writeContract } = useWriteContract();

writeContract({
  address: USDC_ADDRESS,
  abi: ERC20_ABI,
  functionName: 'faucet',
});
```

## 📊 Performance Optimization

- **Code splitting**: Next.js automatic code splitting
- **Image optimization**: Next.js Image component
- **Caching**: TanStack Query caching
- **Lazy loading**: React Suspense for heavy components

## 🔐 Security Best Practices

- ✅ All user inputs validated
- ✅ No private keys in frontend
- ✅ HTTPS only in production
- ✅ Content Security Policy headers
- ✅ No exposed admin functions
- ✅ Safe amount parsing (viem utilities)

## 🤝 Contributing

1. Fork the repository
2. Create feature branch (`git checkout -b feature/amazing-feature`)
3. Commit changes (`git commit -m 'Add amazing feature'`)
4. Push to branch (`git push origin feature/amazing-feature`)
5. Open Pull Request

## 📄 License

UNLICENSED - See main project LICENSE

## 🔗 Links

- **Main README**: `../README.md`
- **Smart Contracts**: `../src/`
- **Documentation**: `../docs/`
- **Base Docs**: https://docs.base.org
- **Wagmi Docs**: https://wagmi.sh
- **RainbowKit Docs**: https://rainbowkit.com

## 💬 Support

- **Issues**: GitHub Issues
- **Discord**: [Coming soon]
- **Twitter**: [@truthyfi](https://twitter.com/truthyfi)
- **Email**: team@truthyfi.xyz

---

**Built with ❤️ using Next.js, wagmi, and Base**
