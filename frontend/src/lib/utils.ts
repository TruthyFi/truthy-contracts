import { type ClassValue, clsx } from "clsx";
import { twMerge } from "tailwind-merge";
import { formatDistanceToNow, format } from "date-fns";

export function cn(...inputs: ClassValue[]) {
  return twMerge(clsx(inputs));
}

// Format USDC (6 decimals) to display
export function formatUSDC(amount: bigint): string {
  const dollars = Number(amount) / 1_000_000;
  return new Intl.NumberFormat('en-US', {
    style: 'currency',
    currency: 'USD',
    minimumFractionDigits: 2,
    maximumFractionDigits: 2,
  }).format(dollars);
}

// Format percentage (1e18 = 100%)
export function formatPercentage(value: bigint): string {
  const percentage = (Number(value) / 1e18) * 100;
  return `${percentage.toFixed(1)}%`;
}

// Format date
export function formatDate(timestamp: number): string {
  return format(new Date(timestamp * 1000), 'MMM d, yyyy');
}

// Format relative time
export function formatRelativeTime(timestamp: number): string {
  return formatDistanceToNow(new Date(timestamp * 1000), { addSuffix: true });
}

// Shorten address
export function shortenAddress(address: string): string {
  return `${address.slice(0, 6)}...${address.slice(-4)}`;
}

// Calculate price from amounts
export function calculatePrice(yesAmount: bigint, noAmount: bigint): { yes: number; no: number } {
  const total = Number(yesAmount + noAmount);
  if (total === 0) return { yes: 0.5, no: 0.5 };

  return {
    yes: Number(yesAmount) / total,
    no: Number(noAmount) / total,
  };
}

// Get category color
export function getCategoryColor(category: string): string {
  const colors: Record<string, string> = {
    crypto: 'bg-orange-500',
    politics: 'bg-blue-500',
    sports: 'bg-green-500',
    defi: 'bg-purple-500',
    social: 'bg-pink-500',
    entertainment: 'bg-yellow-500',
    technology: 'bg-cyan-500',
    other: 'bg-gray-500',
  };
  return colors[category.toLowerCase()] || colors.other;
}

// Get category emoji
export function getCategoryEmoji(category: string): string {
  const emojis: Record<string, string> = {
    crypto: '₿',
    politics: '🗳️',
    sports: '⚽',
    defi: '💎',
    social: '👥',
    entertainment: '🎬',
    technology: '💻',
    other: '📊',
  };
  return emojis[category.toLowerCase()] || emojis.other;
}

// Generate market ID from name
export function generateMarketId(name: string): string {
  const hash = name.toLowerCase().replace(/[^a-z0-9]/g, '-');
  const timestamp = Date.now().toString(36);
  return `${hash}-${timestamp}`;
}

// Validate market creation inputs
export function validateMarketInputs(data: {
  name: string;
  description: string;
  expiresAt: Date;
  initialLiquidity: string;
}): string | null {
  if (!data.name || data.name.length < 10) {
    return "Market name must be at least 10 characters";
  }
  if (!data.description || data.description.length < 20) {
    return "Description must be at least 20 characters";
  }
  if (data.expiresAt <= new Date()) {
    return "Expiry date must be in the future";
  }
  const liquidity = parseFloat(data.initialLiquidity);
  if (isNaN(liquidity) || liquidity < 100) {
    return "Initial liquidity must be at least $100";
  }
  return null;
}
