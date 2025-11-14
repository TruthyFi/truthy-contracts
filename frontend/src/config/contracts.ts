import { Address } from 'viem';
import { baseSepolia, base } from 'viem/chains';

export const CONTRACTS = {
  [baseSepolia.id]: {
    factory: process.env.NEXT_PUBLIC_FACTORY_ADDRESS_SEPOLIA as Address,
    usdc: process.env.NEXT_PUBLIC_USDC_ADDRESS_SEPOLIA as Address,
  },
  [base.id]: {
    factory: process.env.NEXT_PUBLIC_FACTORY_ADDRESS_MAINNET as Address,
    usdc: '0x833589fCD6eDb6E08f4c7C32D4f71b54bdA02913' as Address, // Real USDC on Base
  },
} as const;

export const CREATION_FEE = 5_000_000n; // 5 USDC (6 decimals)
export const PROTOCOL_FEE_RATE = 200; // 2% in basis points

export const MIN_BET = 500_000n; // $0.50
export const MAX_BET = 1_000_000_000n; // $1,000

export const CATEGORIES = [
  'crypto',
  'politics',
  'sports',
  'defi',
  'social',
  'entertainment',
  'technology',
  'other',
] as const;

export type Category = typeof CATEGORIES[number];
