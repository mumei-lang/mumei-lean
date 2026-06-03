#!/bin/bash
set -e

if [[ "$OSTYPE" == "darwin"* ]]; then
  CORES=$(sysctl -n hw.ncpu)
else
  CORES=$(nproc)
fi

echo "Building with $CORES parallel jobs..."

lake update -R
lake exe cache get
LEAN_NUM_THREADS="$CORES" lake build

echo "Build completed successfully"
