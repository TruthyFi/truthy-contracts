'use client';

import { Search } from 'lucide-react';

interface SearchBarProps {
  value: string;
  onChange: (value: string) => void;
}

export function SearchBar({ value, onChange }: SearchBarProps) {
  return (
    <div className="relative">
      <Search className="absolute left-4 top-1/2 transform -translate-y-1/2 h-5 w-5 text-gray-400" />
      <input
        type="text"
        placeholder="Search markets..."
        value={value}
        onChange={(e) => onChange(e.target.value)}
        className="w-full pl-12 pr-4 py-3 bg-slate-800 border border-blue-700/30 rounded-lg text-white placeholder-gray-400 focus:outline-none focus:border-blue-500 transition-colors"
      />
    </div>
  );
}
