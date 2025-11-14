import { getDefaultConfig } from '@rainbow-me/rainbowkit';
import { base, baseSepolia } from 'wagmi/chains';

export const config = getDefaultConfig({
  appName: 'TruthyFi',
  projectId: process.env.NEXT_PUBLIC_WALLETCONNECT_PROJECT_ID || 'YOUR_PROJECT_ID',
  chains: [
    baseSepolia, // Testnet first
    base, // Mainnet
  ],
  ssr: true, // Next.js SSR support
});
