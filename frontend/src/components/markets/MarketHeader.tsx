'use client';

import { useReadContract } from 'wagmi';
import { MARKET_ABI } from '@/config/abis';
import { Address } from 'viem';
import { getCategoryColor, getCategoryEmoji, formatRelativeTime, shortenAddress } from '@/lib/utils';
import { Clock, ExternalLink, User } from 'lucide-react';
import Link from 'next/link';

export function MarketHeader({ address }: { address: Address }) {
  const { data: name } = useReadContract({
    address,
    abi: MARKET_ABI,
    functionName: 'name',
  });

  const { data: description } = useReadContract({
    address,
    abi: MARKET_ABI,
    functionName: 'description',
  });

  const { data: category } = useReadContract({
    address,
    abi: MARKET_ABI,
    functionName: 'category',
  });

  const { data: sourceUrl } = useReadContract({
    address,
    abi: MARKET_ABI,
    functionName: 'sourceUrl',
  });

  const { data: creator } = useReadContract({
    address,
    abi: MARKET_ABI,
    functionName: 'creator',
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

  return (
    <div className="bg-slate-800/50 backdrop-blur border border-blue-700/30 rounded-lg p-8">
      {/* Category & Status */}
      <div className="flex items-center justify-between mb-4">
        <span className={`${getCategoryColor(category as string)} text-white text-sm font-semibold px-3 py-1 rounded-full`}>
          {getCategoryEmoji(category as string)} {category}
        </span>
        {isResolved && (
          <span className="bg-gray-600 text-white text-sm font-semibold px-3 py-1 rounded-full">
            Resolved
          </span>
        )}
      </div>

      {/* Market Name */}
      <h1 className="text-3xl md:text-4xl font-bold text-white mb-4">{name}</h1>

      {/* Description */}
      <p className="text-gray-300 text-lg mb-6">{description}</p>

      {/* Metadata */}
      <div className="flex flex-wrap gap-4 text-sm text-gray-400">
        <div className="flex items-center space-x-2">
          <User className="h-4 w-4" />
          <span>Creator:</span>
          <Link
            href={`/profile/${creator}`}
            className="text-blue-400 hover:text-blue-300"
          >
            {shortenAddress(creator as string)}
          </Link>
        </div>

        <div className="flex items-center space-x-2">
          <Clock className="h-4 w-4" />
          <span>Expires {formatRelativeTime(Number(expiresAt))}</span>
        </div>

        {sourceUrl && (
          <a
            href={sourceUrl as string}
            target="_blank"
            rel="noopener noreferrer"
            className="flex items-center space-x-2 text-blue-400 hover:text-blue-300"
          >
            <ExternalLink className="h-4 w-4" />
            <span>Source</span>
          </a>
        )}
      </div>
    </div>
  );
}
