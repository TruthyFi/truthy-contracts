'use client';

import { useState } from 'react';
import { useAccount, useReadContract, useWriteContract, useWaitForTransactionReceipt, useChainId } from 'wagmi';
import { parseUnits } from 'viem';
import { MARKET_ABI, ERC20_ABI } from '@/config/abis';
import { CONTRACTS } from '@/config/contracts';
import { formatUSDC, formatPercentage } from '@/lib/utils';
import { Address } from 'viem';
import { Loader2, Check, AlertCircle } from 'lucide-react';

export function TradingInterface({ address }: { address: Address }) {
  const { address: userAddress, isConnected } = useAccount();
  const chainId = useChainId();
  const [outcome, setOutcome] = useState<0 | 1>(0); // 0 = YES, 1 = NO
  const [amount, setAmount] = useState('');
  const [approveNeeded, setApproveNeeded] = useState(false);

  const usdcAddress = CONTRACTS[chainId as keyof typeof CONTRACTS]?.usdc;

  // Read user's USDC balance
  const { data: usdcBalance } = useReadContract({
    address: usdcAddress,
    abi: ERC20_ABI,
    functionName: 'balanceOf',
    args: userAddress ? [userAddress] : undefined,
  });

  // Read user's USDC allowance
  const { data: allowance } = useReadContract({
    address: usdcAddress,
    abi: ERC20_ABI,
    functionName: 'allowance',
    args: userAddress ? [userAddress, address] : undefined,
  });

  // Get outcome price
  const { data: price } = useReadContract({
    address,
    abi: MARKET_ABI,
    functionName: 'getOutcomePrice',
    args: [outcome],
  });

  // Preview cost
  const { data: costPreview } = useReadContract({
    address,
    abi: MARKET_ABI,
    functionName: 'previewCostToBuy',
    args: amount ? [outcome, parseUnits(amount, 18)] : undefined,
  });

  // Approve USDC
  const { writeContract: approve, data: approveHash } = useWriteContract();
  const { isLoading: isApproving } = useWaitForTransactionReceipt({ hash: approveHash });

  // Buy outcome
  const { writeContract: buy, data: buyHash, isPending: isBuying } = useWriteContract();
  const { isLoading: isConfirming, isSuccess } = useWaitForTransactionReceipt({ hash: buyHash });

  const handleApprove = async () => {
    if (!usdcAddress) return;
    approve({
      address: usdcAddress,
      abi: ERC20_ABI,
      functionName: 'approve',
      args: [address, parseUnits('1000000', 6)], // Approve 1M USDC
    });
  };

  const handleBuy = async () => {
    if (!amount || !costPreview) return;

    // Check if approval needed
    if (allowance && costPreview > allowance) {
      setApproveNeeded(true);
      return;
    }

    buy({
      address,
      abi: MARKET_ABI,
      functionName: 'buyOutcome',
      args: [outcome, parseUnits(amount, 18)],
    });
  };

  return (
    <div className="bg-slate-800/50 backdrop-blur border border-blue-700/30 rounded-lg p-6 space-y-4">
      <h3 className="text-xl font-bold text-white mb-4">Trade</h3>

      {!isConnected ? (
        <div className="text-center py-8 text-gray-400">
          <p>Connect wallet to trade</p>
        </div>
      ) : (
        <>
          {/* Outcome Selection */}
          <div className="grid grid-cols-2 gap-2">
            <button
              onClick={() => setOutcome(0)}
              className={`py-3 px-4 rounded-lg font-semibold transition-all ${
                outcome === 0
                  ? 'bg-yes text-white'
                  : 'bg-slate-700 text-gray-300 hover:bg-slate-600'
              }`}
            >
              YES {price && formatPercentage(price)}
            </button>
            <button
              onClick={() => setOutcome(1)}
              className={`py-3 px-4 rounded-lg font-semibold transition-all ${
                outcome === 1
                  ? 'bg-no text-white'
                  : 'bg-slate-700 text-gray-300 hover:bg-slate-600'
              }`}
            >
              NO {price && formatPercentage(price)}
            </button>
          </div>

          {/* Amount Input */}
          <div>
            <label className="block text-sm font-medium text-gray-300 mb-2">
              Amount (shares)
            </label>
            <input
              type="number"
              value={amount}
              onChange={(e) => setAmount(e.target.value)}
              placeholder="0.0"
              className="w-full px-4 py-3 bg-slate-700 border border-blue-700/30 rounded-lg text-white focus:outline-none focus:border-blue-500"
            />
          </div>

          {/* Cost Preview */}
          {costPreview && (
            <div className="bg-slate-700/50 rounded-lg p-4 space-y-2">
              <div className="flex justify-between text-sm">
                <span className="text-gray-400">Cost:</span>
                <span className="text-white font-semibold">{formatUSDC(costPreview)}</span>
              </div>
              <div className="flex justify-between text-sm">
                <span className="text-gray-400">Balance:</span>
                <span className="text-white">{formatUSDC(usdcBalance || 0n)}</span>
              </div>
            </div>
          )}

          {/* Action Button */}
          {approveNeeded ? (
            <button
              onClick={handleApprove}
              disabled={isApproving}
              className="w-full bg-yellow-600 hover:bg-yellow-700 disabled:bg-gray-600 text-white font-semibold py-3 px-4 rounded-lg transition-colors flex items-center justify-center space-x-2"
            >
              {isApproving ? (
                <>
                  <Loader2 className="h-5 w-5 animate-spin" />
                  <span>Approving...</span>
                </>
              ) : (
                <span>Approve USDC</span>
              )}
            </button>
          ) : (
            <button
              onClick={handleBuy}
              disabled={!amount || isBuying || isConfirming || isSuccess}
              className={`w-full font-semibold py-3 px-4 rounded-lg transition-colors flex items-center justify-center space-x-2 ${
                outcome === 0
                  ? 'bg-yes hover:bg-yes-dark'
                  : 'bg-no hover:bg-no-dark'
              } disabled:bg-gray-600 text-white`}
            >
              {isConfirming || isBuying ? (
                <>
                  <Loader2 className="h-5 w-5 animate-spin" />
                  <span>Processing...</span>
                </>
              ) : isSuccess ? (
                <>
                  <Check className="h-5 w-5" />
                  <span>Success!</span>
                </>
              ) : (
                <span>Buy {outcome === 0 ? 'YES' : 'NO'}</span>
              )}
            </button>
          )}

          {/* Info */}
          <div className="text-xs text-gray-400 text-center">
            <p>Trades have a 2% protocol fee</p>
            <p>Min: $0.50 | Max: $1,000 per trade</p>
          </div>
        </>
      )}
    </div>
  );
}
