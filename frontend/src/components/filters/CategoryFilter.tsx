'use client';

import { CATEGORIES } from '@/config/contracts';
import { getCategoryEmoji } from '@/lib/utils';

interface CategoryFilterProps {
  selectedCategory: string;
  onSelectCategory: (category: string) => void;
}

export function CategoryFilter({ selectedCategory, onSelectCategory }: CategoryFilterProps) {
  return (
    <div className="flex flex-wrap gap-2">
      <button
        onClick={() => onSelectCategory('all')}
        className={`px-4 py-2 rounded-lg font-medium transition-all ${
          selectedCategory === 'all'
            ? 'bg-blue-600 text-white'
            : 'bg-slate-800 text-gray-300 hover:bg-slate-700'
        }`}
      >
        All
      </button>
      {CATEGORIES.map((category) => (
        <button
          key={category}
          onClick={() => onSelectCategory(category)}
          className={`px-4 py-2 rounded-lg font-medium transition-all capitalize ${
            selectedCategory === category
              ? 'bg-blue-600 text-white'
              : 'bg-slate-800 text-gray-300 hover:bg-slate-700'
          }`}
        >
          {getCategoryEmoji(category)} {category}
        </button>
      ))}
    </div>
  );
}
