'use client';

import { useReadContract } from 'wagmi';
import { MARKET_ABI } from '@/config/abis';
import { Address } from 'viem';
import { formatUSDC, formatDate } from '@/lib/utils';
import { DollarSign, Users, Calendar, TrendingUp } from 'lucide-react';

export function MarketInfo({ address }: { address: Address }) {
  const { data: totalLiquidity } = useReadContract({
    address,
    abi: MARKET_ABI,
    functionName: 'getTotalLiquidity',
  });

  const { data: totalVolume } = useReadContract({
    address,
    abi: MARKET_ABI,
    functionName: 'totalVolume',
  });

  const { data: expiresAt } = useReadContract({
    address,
    abi: MARKET_ABI,
    functionName: 'expiresAt',
  });

  const { data: minBet } = useReadContract({
    address,
    abi: MARKET_ABI,
    functionName: 'minBet',
  });

  const { data: maxBet } = useReadContract({
    address,
    abi: MARKET_ABI,
    functionName: 'maxBet',
  });

  const infoItems = [
    {
      label: 'Total Liquidity',
      value: totalLiquidity ? formatUSDC(totalLiquidity) : '$0',
      icon: DollarSign,
      color: 'text-blue-400',
    },
    {
      label: 'Total Volume',
      value: totalVolume ? formatUSDC(totalVolume) : '$0',
      icon: TrendingUp,
      color: 'text-green-400',
    },
    {
      label: 'Expires',
      value: expiresAt ? formatDate(Number(expiresAt)) : 'N/A',
      icon: Calendar,
      color: 'text-yellow-400',
    },
    {
      label: 'Bet Limits',
      value: minBet && maxBet ? `${formatUSDC(minBet)} - ${formatUSDC(maxBet)}` : 'N/A',
      icon: Users,
      color: 'text-purple-400',
    },
  ];

  return (
    <div className="bg-slate-800/50 backdrop-blur border border-blue-700/30 rounded-lg p-6">
      <h2 className="text-xl font-bold text-white mb-6">Market Information</h2>

      <div className="grid grid-cols-1 md:grid-cols-2 gap-4">
        {infoItems.map((item) => {
          const Icon = item.icon;
          return (
            <div
              key={item.label}
              className="flex items-center space-x-3 p-4 bg-slate-700/50 rounded-lg"
            >
              <Icon className={`h-5 w-5 ${item.color}`} />
              <div>
                <div className="text-sm text-gray-400">{item.label}</div>
                <div className="text-white font-semibold">{item.value}</div>
              </div>
            </div>
          );
        })}
      </div>
    </div>
  );
}
