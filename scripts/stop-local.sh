#!/bin/bash

# Stop local testing environment

echo "🛑 Stopping TruthyFi Local Test Environment"
echo "==========================================="
echo ""

# Kill Anvil
if [ -f "/tmp/truthy-anvil.pid" ]; then
    ANVIL_PID=$(cat /tmp/truthy-anvil.pid)
    if kill -0 $ANVIL_PID 2>/dev/null; then
        echo "Stopping Anvil (PID: $ANVIL_PID)..."
        kill $ANVIL_PID
        rm /tmp/truthy-anvil.pid
        echo "✅ Anvil stopped"
    else
        echo "ℹ️  Anvil is not running"
        rm /tmp/truthy-anvil.pid
    fi
else
    # Try to find and kill any anvil process
    if pgrep -x "anvil" > /dev/null; then
        echo "Found running Anvil, stopping..."
        killall anvil
        echo "✅ Anvil stopped"
    else
        echo "ℹ️  No Anvil process found"
    fi
fi

# Check for any process on port 8545
if lsof -Pi :8545 -sTCP:LISTEN -t >/dev/null 2>&1; then
    echo "⚠️  Port 8545 is still in use"
    echo "Process info:"
    lsof -i :8545
    read -p "Kill this process? (y/n) " -n 1 -r
    echo
    if [[ $REPLY =~ ^[Yy]$ ]]; then
        kill -9 $(lsof -t -i:8545)
        echo "✅ Port 8545 freed"
    fi
fi

# Clean up logs
if [ -f "/tmp/anvil.log" ]; then
    rm /tmp/anvil.log
    echo "✅ Logs cleaned"
fi

echo ""
echo "✅ Cleanup complete!"
