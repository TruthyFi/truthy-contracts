'use client';

import Link from 'next/link';
import { ConnectButton } from '@rainbow-me/rainbowkit';
import { TrendingUp } from 'lucide-react';

export function Header() {
  return (
    <header className="border-b border-blue-800/50 bg-slate-900/50 backdrop-blur-sm sticky top-0 z-50">
      <div className="container mx-auto px-4">
        <div className="flex items-center justify-between h-16">
          {/* Logo */}
          <Link href="/" className="flex items-center space-x-2 hover:opacity-80 transition-opacity">
            <TrendingUp className="h-8 w-8 text-blue-400" />
            <div>
              <h1 className="text-xl font-bold text-white">TruthyFi</h1>
              <p className="text-xs text-blue-300">Put your money where your mouth is</p>
            </div>
          </Link>

          {/* Navigation */}
          <nav className="hidden md:flex items-center space-x-6">
            <Link
              href="/"
              className="text-gray-300 hover:text-white transition-colors font-medium"
            >
              Markets
            </Link>
            <Link
              href="/create"
              className="text-gray-300 hover:text-white transition-colors font-medium"
            >
              Create Market
            </Link>
            <Link
              href="/profile"
              className="text-gray-300 hover:text-white transition-colors font-medium"
            >
              Profile
            </Link>
            <a
              href="https://warpcast.com/truthyfi"
              target="_blank"
              rel="noopener noreferrer"
              className="text-gray-300 hover:text-white transition-colors font-medium"
            >
              Farcaster
            </a>
          </nav>

          {/* Wallet Connect */}
          <ConnectButton />
        </div>
      </div>
    </header>
  );
}
