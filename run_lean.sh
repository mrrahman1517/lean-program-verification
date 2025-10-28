#!/bin/bash

# Script to easily run any Lean file
# Usage: ./run_lean.sh filename.lean

if [ $# -eq 0 ]; then
    echo "Usage: $0 <lean_file>"
    echo "Example: $0 myprogram.lean"
    exit 1
fi

LEAN_FILE="$1"

if [ ! -f "$LEAN_FILE" ]; then
    echo "Error: File '$LEAN_FILE' not found!"
    exit 1
fi

echo "Running $LEAN_FILE..."
lean --run "$LEAN_FILE"