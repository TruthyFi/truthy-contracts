'use client';

import { useReadContract } from 'wagmi';
import { MARKET_ABI } from '@/config/abis';
import { Address } from 'viem';
import { formatPercentage, calculatePrice } from '@/lib/utils';
import { TrendingUp } from 'lucide-react';

export function MarketChart({ address }: { address: Address }) {
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

  const prices = yesLiquidity && noLiquidity
    ? calculatePrice(yesLiquidity, noLiquidity)
    : { yes: 0.5, no: 0.5 };

  return (
    <div className="bg-slate-800/50 backdrop-blur border border-blue-700/30 rounded-lg p-6">
      <div className="flex items-center justify-between mb-6">
        <h2 className="text-xl font-bold text-white">Current Odds</h2>
        <TrendingUp className="h-5 w-5 text-blue-400" />
      </div>

      {/* Big Percentages */}
      <div className="grid grid-cols-2 gap-4 mb-6">
        <div className="text-center p-6 bg-yes/20 rounded-lg border border-yes">
          <div className="text-4xl font-bold text-yes mb-2">
            {formatPercentage(BigInt(Math.floor(prices.yes * 1e18)))}
          </div>
          <div className="text-gray-300 font-medium">YES</div>
        </div>
        <div className="text-center p-6 bg-no/20 rounded-lg border border-no">
          <div className="text-4xl font-bold text-no mb-2">
            {formatPercentage(BigInt(Math.floor(prices.no * 1e18)))}
          </div>
          <div className="text-gray-300 font-medium">NO</div>
        </div>
      </div>

      {/* Visual Bar */}
      <div className="w-full bg-slate-700 rounded-full h-4 overflow-hidden flex">
        <div
          className="bg-yes transition-all duration-300"
          style={{ width: `${prices.yes * 100}%` }}
        />
        <div
          className="bg-no transition-all duration-300"
          style={{ width: `${prices.no * 100}%` }}
        />
      </div>

      {/* Note */}
      <p className="text-sm text-gray-400 mt-4 text-center">
        Prices update based on supply and demand
      </p>
    </div>
  );
}
