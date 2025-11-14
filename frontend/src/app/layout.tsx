import type { Metadata } from "next";
import { Inter } from "next/font/google";
import "./globals.css";
import { Web3Provider } from "@/providers/Web3Provider";
import { Header } from "@/components/layout/Header";

const inter = Inter({ subsets: ["latin"] });

export const metadata: Metadata = {
  title: "TruthyFi - Social Prediction Markets",
  description: "Put your money where your mouth is. Create and bet on prediction markets linked to social posts.",
  icons: {
    icon: "/favicon.ico",
  },
};

export default function RootLayout({
  children,
}: Readonly<{
  children: React.ReactNode;
}>) {
  return (
    <html lang="en">
      <body className={inter.className}>
        <Web3Provider>
          <div className="min-h-screen bg-gradient-to-br from-slate-900 via-blue-900 to-slate-900">
            <Header />
            <main className="container mx-auto px-4 py-8">
              {children}
            </main>
          </div>
        </Web3Provider>
      </body>
    </html>
  );
}
