'use client';

import { useReadContract, useChainId } from 'wagmi';
import { CONTRACTS } from '@/config/contracts';
import { FACTORY_ABI } from '@/config/abis';
import { TrendingUp, Users, DollarSign, Activity } from 'lucide-react';

export function StatsOverview() {
  const chainId = useChainId();

  const { data: totalMarkets } = useReadContract({
    address: CONTRACTS[chainId as keyof typeof CONTRACTS]?.factory,
    abi: FACTORY_ABI,
    functionName: 'getTotalMarkets',
  });

  const stats = [
    {
      label: 'Total Markets',
      value: totalMarkets ? totalMarkets.toString() : '0',
      icon: TrendingUp,
      color: 'text-blue-400',
      bgColor: 'bg-blue-900/30',
    },
    {
      label: 'Active Traders',
      value: '234', // TODO: Calculate from events
      icon: Users,
      color: 'text-green-400',
      bgColor: 'bg-green-900/30',
    },
    {
      label: 'Total Volume',
      value: '$12.4K', // TODO: Calculate from markets
      icon: DollarSign,
      color: 'text-yellow-400',
      bgColor: 'bg-yellow-900/30',
    },
    {
      label: '24h Volume',
      value: '$2.1K', // TODO: Calculate from recent activity
      icon: Activity,
      color: 'text-purple-400',
      bgColor: 'bg-purple-900/30',
    },
  ];

  return (
    <div className="grid grid-cols-2 md:grid-cols-4 gap-4">
      {stats.map((stat) => {
        const Icon = stat.icon;
        return (
          <div
            key={stat.label}
            className={`${stat.bgColor} border border-${stat.color.replace('text-', '')}/30 rounded-lg p-4`}
          >
            <div className="flex items-center justify-between mb-2">
              <Icon className={`h-5 w-5 ${stat.color}`} />
            </div>
            <div className="text-2xl font-bold text-white mb-1">{stat.value}</div>
            <div className="text-sm text-gray-400">{stat.label}</div>
          </div>
        );
      })}
    </div>
  );
}
