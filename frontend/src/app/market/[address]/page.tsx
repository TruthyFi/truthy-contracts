'use client';

import { use } from 'react';
import { useReadContract } from 'wagmi';
import { MARKET_ABI } from '@/config/abis';
import { MarketHeader } from '@/components/markets/MarketHeader';
import { TradingInterface } from '@/components/trading/TradingInterface';
import { MarketChart } from '@/components/markets/MarketChart';
import { MarketInfo } from '@/components/markets/MarketInfo';
import { Address } from 'viem';
import { Loader2 } from 'lucide-react';

export default function MarketPage({ params }: { params: Promise<{ address: string }> }) {
  const resolvedParams = use(params);
  const marketAddress = resolvedParams.address as Address;

  const { data: name, isLoading } = useReadContract({
    address: marketAddress,
    abi: MARKET_ABI,
    functionName: 'name',
  });

  if (isLoading) {
    return (
      <div className="flex items-center justify-center min-h-screen">
        <Loader2 className="h-12 w-12 animate-spin text-blue-400" />
      </div>
    );
  }

  if (!name) {
    return (
      <div className="text-center py-20">
        <p className="text-gray-400 text-lg">Market not found</p>
      </div>
    );
  }

  return (
    <div className="max-w-7xl mx-auto space-y-8">
      <MarketHeader address={marketAddress} />

      <div className="grid grid-cols-1 lg:grid-cols-3 gap-8">
        {/* Main Content - 2/3 width */}
        <div className="lg:col-span-2 space-y-6">
          <MarketChart address={marketAddress} />
          <MarketInfo address={marketAddress} />
        </div>

        {/* Trading Panel - 1/3 width */}
        <div className="lg:col-span-1">
          <div className="sticky top-24">
            <TradingInterface address={marketAddress} />
          </div>
        </div>
      </div>
    </div>
  );
}
