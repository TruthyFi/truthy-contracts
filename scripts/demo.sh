#!/bin/bash

# Quick demo script for TruthyFi
# Shows a complete trading flow

set -e

echo "🎬 TruthyFi Demo Script"
echo "======================="
echo ""
echo "This will demonstrate a complete prediction market trade flow."
echo ""

# Check prerequisites
if ! kill -0 $(cat /tmp/truthy-anvil.pid 2>/dev/null) 2>/dev/null; then
    echo "❌ Anvil is not running"
    echo "Run: bash scripts/local-test.sh"
    exit 1
fi

if [ ! -f "deployments/31337.json" ]; then
    echo "❌ Contracts not deployed"
    echo "Run: bash scripts/local-test.sh"
    exit 1
fi

# Load deployment addresses
if command -v jq &> /dev/null; then
    FACTORY_ADDRESS=$(jq -r '.factory' deployments/31337.json)
    USDC_ADDRESS=$(jq -r '.usdc' deployments/31337.json)
else
    FACTORY_ADDRESS=$(grep -o '"factory": "[^"]*' deployments/31337.json | cut -d'"' -f4)
    USDC_ADDRESS=$(grep -o '"usdc": "[^"]*' deployments/31337.json | cut -d'"' -f4)
fi

PRIVATE_KEY=0xac0974bec39a17e36ba4a6b4d238ff944bacb478cbed5efcae784d7bf4f2ff80
TRADER=0xf39Fd6e51aad88F6F4ce6aB8827279cffFb92266

echo "📊 Demo Setup:"
echo "  Factory: $FACTORY_ADDRESS"
echo "  USDC: $USDC_ADDRESS"
echo "  Trader: $TRADER"
echo ""

# Get first market
echo "🔍 Finding market..."
MARKETS_HEX=$(cast call $FACTORY_ADDRESS "getAllMarkets()(address[])" --rpc-url http://localhost:8545)
MARKET_ADDRESS=$(echo $MARKETS_HEX | cut -d',' -f1 | xargs)

if [ -z "$MARKET_ADDRESS" ] || [ "$MARKET_ADDRESS" == "0x0000000000000000000000000000000000000000" ]; then
    echo "❌ No markets found"
    echo "Run: forge script script/CreateDemoMarket.s.sol:CreateDemoMarket --rpc-url http://localhost:8545 --broadcast"
    exit 1
fi

echo "  Market: $MARKET_ADDRESS"
echo ""

# Get market info
echo "📈 Market Information:"
MARKET_NAME=$(cast call $MARKET_ADDRESS "name()(string)" --rpc-url http://localhost:8545)
YES_PRICE=$(cast call $MARKET_ADDRESS "getOutcomePrice(uint256)(uint256)" 0 --rpc-url http://localhost:8545)
NO_PRICE=$(cast call $MARKET_ADDRESS "getOutcomePrice(uint256)(uint256)" 1 --rpc-url http://localhost:8545)

# Convert prices to percentages
YES_PERCENT=$(echo "scale=2; $YES_PRICE / 10000000000000000" | bc)
NO_PERCENT=$(echo "scale=2; $NO_PRICE / 10000000000000000" | bc)

echo "  Name: $MARKET_NAME"
echo "  YES Price: $YES_PERCENT%"
echo "  NO Price: $NO_PERCENT%"
echo ""

# Get USDC from faucet
echo "💰 Getting test USDC..."
cast send $USDC_ADDRESS \
  "faucet()" \
  --rpc-url http://localhost:8545 \
  --private-key $PRIVATE_KEY \
  --silent

USDC_BALANCE=$(cast call $USDC_ADDRESS "balanceOf(address)(uint256)" $TRADER --rpc-url http://localhost:8545)
USDC_FORMATTED=$(echo "scale=2; $USDC_BALANCE / 1000000" | bc)
echo "  USDC Balance: $USDC_FORMATTED USDC"
echo ""

# Approve USDC
echo "✅ Approving USDC..."
cast send $USDC_ADDRESS \
  "approve(address,uint256)" \
  $MARKET_ADDRESS \
  $(cast max-uint256) \
  --rpc-url http://localhost:8545 \
  --private-key $PRIVATE_KEY \
  --silent
echo "  Approved!"
echo ""

# Buy YES tokens
BUY_AMOUNT="10000000000000000000" # 10 tokens
echo "🛒 Buying 10 YES tokens..."

# Preview cost
COST_PREVIEW=$(cast call $MARKET_ADDRESS "previewCostToBuy(uint256,uint256)(uint256)" 0 $BUY_AMOUNT --rpc-url http://localhost:8545)
COST_USDC=$(echo "scale=2; $COST_PREVIEW / 1000000" | bc)
echo "  Estimated cost: $COST_USDC USDC"

# Execute buy
cast send $MARKET_ADDRESS \
  "buyOutcome(uint256,uint256)" \
  0 \
  $BUY_AMOUNT \
  --rpc-url http://localhost:8545 \
  --private-key $PRIVATE_KEY \
  --silent

echo "  ✅ Purchase complete!"
echo ""

# Get updated prices
echo "📊 Updated Prices:"
NEW_YES_PRICE=$(cast call $MARKET_ADDRESS "getOutcomePrice(uint256)(uint256)" 0 --rpc-url http://localhost:8545)
NEW_NO_PRICE=$(cast call $MARKET_ADDRESS "getOutcomePrice(uint256)(uint256)" 1 --rpc-url http://localhost:8545)

NEW_YES_PERCENT=$(echo "scale=2; $NEW_YES_PRICE / 10000000000000000" | bc)
NEW_NO_PERCENT=$(echo "scale=2; $NEW_NO_PRICE / 10000000000000000" | bc)

echo "  YES Price: $NEW_YES_PERCENT% (was $YES_PERCENT%)"
echo "  NO Price: $NEW_NO_PERCENT% (was $NO_PERCENT%)"
echo ""

# Calculate price impact
YES_CHANGE=$(echo "scale=2; ($NEW_YES_PERCENT - $YES_PERCENT) / $YES_PERCENT * 100" | bc)
echo "  Price Impact: +$YES_CHANGE%"
echo ""

# Check position
OUTCOME_TOKEN=$(cast call $MARKET_ADDRESS "getOutcomeToken(uint256)(address)" 0 --rpc-url http://localhost:8545)
TOKEN_BALANCE=$(cast call $OUTCOME_TOKEN "balanceOf(address)(uint256)" $TRADER --rpc-url http://localhost:8545)
TOKEN_FORMATTED=$(echo "scale=2; $TOKEN_BALANCE / 1000000000000000000" | bc)

echo "💼 Your Position:"
echo "  YES Tokens: $TOKEN_FORMATTED"
echo "  Entry Price: $YES_PERCENT%"
echo "  Current Price: $NEW_YES_PERCENT%"
echo ""

# Sell half
SELL_AMOUNT="5000000000000000000" # 5 tokens
echo "💸 Selling 5 YES tokens..."

PROCEEDS_PREVIEW=$(cast call $MARKET_ADDRESS "previewProceedsFromSale(uint256,uint256)(uint256)" 0 $SELL_AMOUNT --rpc-url http://localhost:8545)
PROCEEDS_USDC=$(echo "scale=2; $PROCEEDS_PREVIEW / 1000000" | bc)
echo "  Estimated proceeds: $PROCEEDS_USDC USDC"

cast send $MARKET_ADDRESS \
  "sellOutcome(uint256,uint256)" \
  0 \
  $SELL_AMOUNT \
  --rpc-url http://localhost:8545 \
  --private-key $PRIVATE_KEY \
  --silent

echo "  ✅ Sale complete!"
echo ""

# Final prices
echo "📊 Final Prices:"
FINAL_YES_PRICE=$(cast call $MARKET_ADDRESS "getOutcomePrice(uint256)(uint256)" 0 --rpc-url http://localhost:8545)
FINAL_NO_PRICE=$(cast call $MARKET_ADDRESS "getOutcomePrice(uint256)(uint256)" 1 --rpc-url http://localhost:8545)

FINAL_YES_PERCENT=$(echo "scale=2; $FINAL_YES_PRICE / 10000000000000000" | bc)
FINAL_NO_PERCENT=$(echo "scale=2; $FINAL_NO_PRICE / 10000000000000000" | bc)

echo "  YES Price: $FINAL_YES_PERCENT%"
echo "  NO Price: $FINAL_NO_PERCENT%"
echo ""

# Final position
FINAL_TOKEN_BALANCE=$(cast call $OUTCOME_TOKEN "balanceOf(address)(uint256)" $TRADER --rpc-url http://localhost:8545)
FINAL_TOKEN_FORMATTED=$(echo "scale=2; $FINAL_TOKEN_BALANCE / 1000000000000000000" | bc)
FINAL_USDC_BALANCE=$(cast call $USDC_ADDRESS "balanceOf(address)(uint256)" $TRADER --rpc-url http://localhost:8545)
FINAL_USDC_FORMATTED=$(echo "scale=2; $FINAL_USDC_BALANCE / 1000000" | bc)

echo "💼 Final Position:"
echo "  YES Tokens: $FINAL_TOKEN_FORMATTED"
echo "  USDC Balance: $FINAL_USDC_FORMATTED USDC"
echo ""

echo "================================"
echo "✅ Demo Complete!"
echo "================================"
echo ""
echo "📝 Summary:"
echo "  ✅ Got test USDC from faucet"
echo "  ✅ Approved USDC for trading"
echo "  ✅ Bought 10 YES tokens"
echo "  ✅ Sold 5 YES tokens"
echo "  ✅ Prices updated based on trades"
echo ""
echo "🌐 Try it in the UI:"
echo "  1. cd frontend && npm run dev"
echo "  2. Open http://localhost:3000"
echo "  3. Connect MetaMask with test account"
echo "  4. Browse and trade!"
echo ""
