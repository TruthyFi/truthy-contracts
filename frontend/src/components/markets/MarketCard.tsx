'use client';

import Link from 'next/link';
import { useReadContract } from 'wagmi';
import { MARKET_ABI } from '@/config/abis';
import { formatRelativeTime, formatPercentage, getCategoryColor, getCategoryEmoji, calculatePrice } from '@/lib/utils';
import { Clock, TrendingUp, Users } from 'lucide-react';
import { Address } from 'viem';

interface MarketCardProps {
  address: Address;
}

export function MarketCard({ address }: MarketCardProps) {
  // Fetch market data
  const { data: name } = useReadContract({
    address,
    abi: MARKET_ABI,
    functionName: 'name',
  });

  const { data: category } = useReadContract({
    address,
    abi: MARKET_ABI,
    functionName: 'category',
  });

  const { data: expiresAt } = useReadContract({
    address,
    abi: MARKET_ABI,
    functionName: 'expiresAt',
  });

  const { data: isResolved } = useReadContract({
    address,
    abi: MARKET_ABI,
    functionName: 'isResolved',
  });

  const { data: yesLiquidity } = useReadContract({
    address,
    abi: MARKET_ABI,
    functionName: 'getOutcomeLiquidity',
    args: [0],
  });

  const { data: noLiquidity } = useReadContract({
    address,
    abi: MARKET_ABI,
    functionName: 'getOutcomeLiquidity',
    args: [1],
  });

  const { data: totalVolume } = useReadContract({
    address,
    abi: MARKET_ABI,
    functionName: 'totalVolume',
  });

  if (!name) return null;

  const prices = yesLiquidity && noLiquidity
    ? calculatePrice(yesLiquidity, noLiquidity)
    : { yes: 0.5, no: 0.5 };

  return (
    <Link href={`/market/${address}`}>
      <div className="bg-slate-800/50 backdrop-blur border border-blue-700/30 rounded-lg p-6 hover:border-blue-500/50 transition-all hover:shadow-lg hover:shadow-blue-500/20 cursor-pointer">
        {/* Category Badge */}
        <div className="flex items-center justify-between mb-3">
          <span className={`${getCategoryColor(category as string)} text-white text-xs font-semibold px-3 py-1 rounded-full`}>
            {getCategoryEmoji(category as string)} {category}
          </span>
          {isResolved && (
            <span className="bg-gray-600 text-white text-xs font-semibold px-3 py-1 rounded-full">
              Resolved
            </span>
          )}
        </div>

        {/* Market Name */}
        <h3 className="text-lg font-semibold text-white mb-4 line-clamp-2 min-h-[3.5rem]">
          {name}
        </h3>

        {/* Probabilities */}
        <div className="space-y-2 mb-4">
          <div className="flex items-center justify-between">
            <span className="text-gray-400 text-sm">YES</span>
            <span className="text-yes font-bold">{formatPercentage(BigInt(Math.floor(prices.yes * 1e18)))}</span>
          </div>
          <div className="w-full bg-slate-700 rounded-full h-2 overflow-hidden">
            <div
              className="bg-yes h-full transition-all duration-300"
              style={{ width: `${prices.yes * 100}%` }}
            />
          </div>
          <div className="flex items-center justify-between">
            <span className="text-gray-400 text-sm">NO</span>
            <span className="text-no font-bold">{formatPercentage(BigInt(Math.floor(prices.no * 1e18)))}</span>
          </div>
        </div>

        {/* Footer Stats */}
        <div className="flex items-center justify-between text-sm text-gray-400 pt-4 border-t border-slate-700">
          <div className="flex items-center space-x-1">
            <Clock className="h-4 w-4" />
            <span>{formatRelativeTime(Number(expiresAt))}</span>
          </div>
          {totalVolume && Number(totalVolume) > 0 && (
            <div className="flex items-center space-x-1">
              <TrendingUp className="h-4 w-4" />
              <span>${(Number(totalVolume) / 1e6).toFixed(0)}</span>
            </div>
          )}
        </div>
      </div>
    </Link>
  );
}
