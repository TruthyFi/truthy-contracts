'use client';

import { useState } from 'react';
import { useReadContract, useChainId } from 'wagmi';
import { CONTRACTS } from '@/config/contracts';
import { FACTORY_ABI } from '@/config/abis';
import { MarketCard } from '@/components/markets/MarketCard';
import { CategoryFilter } from '@/components/filters/CategoryFilter';
import { SearchBar } from '@/components/filters/SearchBar';
import { StatsOverview } from '@/components/stats/StatsOverview';
import { Loader2 } from 'lucide-react';

export default function Home() {
  const chainId = useChainId();
  const [selectedCategory, setSelectedCategory] = useState<string>('all');
  const [searchQuery, setSearchQuery] = useState('');

  // Fetch all markets
  const { data: markets, isLoading } = useReadContract({
    address: CONTRACTS[chainId as keyof typeof CONTRACTS]?.factory,
    abi: FACTORY_ABI,
    functionName: 'getAllMarkets',
  });

  return (
    <div className="space-y-8">
      {/* Hero Section */}
      <div className="text-center space-y-4">
        <h1 className="text-5xl md:text-6xl font-bold text-white">
          Social Prediction Markets
        </h1>
        <p className="text-xl text-gray-300 max-w-2xl mx-auto">
          Create markets on any claim. Bet with micro-amounts. Build your reputation through accurate predictions.
        </p>
      </div>

      {/* Stats Overview */}
      <StatsOverview />

      {/* Filters */}
      <div className="flex flex-col md:flex-row gap-4">
        <div className="flex-1">
          <SearchBar value={searchQuery} onChange={setSearchQuery} />
        </div>
        <CategoryFilter
          selectedCategory={selectedCategory}
          onSelectCategory={setSelectedCategory}
        />
      </div>

      {/* Markets Grid */}
      {isLoading ? (
        <div className="flex items-center justify-center py-20">
          <Loader2 className="h-12 w-12 animate-spin text-blue-400" />
        </div>
      ) : !markets || markets.length === 0 ? (
        <div className="text-center py-20">
          <p className="text-gray-400 text-lg">No markets found. Create the first one!</p>
        </div>
      ) : (
        <div className="grid grid-cols-1 md:grid-cols-2 lg:grid-cols-3 gap-6">
          {markets.map((marketAddress) => (
            <MarketCard key={marketAddress} address={marketAddress} />
          ))}
        </div>
      )}
    </div>
  );
}
