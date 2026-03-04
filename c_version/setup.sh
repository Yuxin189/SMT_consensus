#!/bin/bash
# Setup script for CEGIS Consensus Protocol Synthesis (C version)
# Checks dependencies, installs if needed, and builds the project

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

# Idempotent: skip if already built
if [ -x "./cegis" ]; then
    echo "[OK] cegis already built, skipping setup"
    exit 0
fi

echo "=== CEGIS C Version Setup ==="

# Check for C compiler
if command -v gcc &>/dev/null; then
    echo "[OK] gcc found: $(gcc --version | head -1)"
elif command -v clang &>/dev/null; then
    echo "[OK] clang found (using as CC)"
    export CC=clang
else
    echo "[ERROR] No C compiler (gcc/clang) found. Please install one."
    exit 1
fi

# Check for Z3
check_z3() {
    if pkg-config --exists z3 2>/dev/null; then
        return 0
    fi
    if [ -f /usr/local/include/z3.h ] || [ -f /opt/homebrew/include/z3.h ]; then
        return 0
    fi
    if python3 -c "import z3" 2>/dev/null; then
        return 0
    fi
    return 1
}

if check_z3; then
    echo "[OK] Z3 found"
else
    echo "[WARN] Z3 not found. Installing..."
    if [[ "$OSTYPE" == "darwin"* ]]; then
        if command -v brew &>/dev/null; then
            brew install z3
        else
            echo "[ERROR] Homebrew not found. Install Z3 manually: brew install z3"
            exit 1
        fi
    elif command -v apt-get &>/dev/null; then
        sudo apt update
        sudo apt install -y z3 libz3-dev
    else
        echo "[ERROR] Unsupported OS. Please install Z3 manually."
        echo "  macOS: brew install z3"
        echo "  Ubuntu/Debian: sudo apt install z3 libz3-dev"
        exit 1
    fi
fi

# Build
echo ""
echo "=== Building ==="
make clean 2>/dev/null || true
make

echo ""
echo "[OK] Setup complete. Run: make run"
