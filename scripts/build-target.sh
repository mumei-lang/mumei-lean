#!/bin/bash
set -e

if [ -z "$1" ]; then
  echo "Usage: $0 <target_name>"
  echo "Examples:"
  echo "  $0 MumeiLean           # Build MumeiLean library only"
  echo "  $0 MumeiLean.Basic     # Build specific module"
  echo "  $0 Generated           # Build Generated library only"
  exit 1
fi

TARGET=$1

if [[ "$OSTYPE" == "darwin"* ]]; then
  CORES=$(sysctl -n hw.ncpu)
else
  CORES=$(nproc)
fi

echo "Building target: $TARGET with $CORES parallel jobs..."

lake update -R
lake exe cache get
LEAN_NUM_THREADS="$CORES" lake build "$TARGET"

echo "Build of $TARGET completed successfully"
