#!/bin/bash

# Script to add a Lean file as an executable to lakefile.lean and run it
# Usage: ./add_and_run.sh filename.lean

if [ $# -eq 0 ]; then
    echo "Usage: $0 <lean_file>"
    echo "Example: $0 myprogram.lean"
    exit 1
fi

LEAN_FILE="$1"
BASENAME=$(basename "$LEAN_FILE" .lean)

if [ ! -f "$LEAN_FILE" ]; then
    echo "Error: File '$LEAN_FILE' not found!"
    exit 1
fi

# Check if the executable already exists in lakefile.lean
if grep -q "lean_exe «$BASENAME»" lakefile.lean; then
    echo "Executable '$BASENAME' already exists in lakefile.lean"
else
    echo "Adding '$BASENAME' to lakefile.lean..."
    # Insert the new executable before the require mathlib line
    sed -i.bak "/require mathlib/i\\
lean_exe «$BASENAME» where\\
  root := \`$BASENAME\\
" lakefile.lean
    echo "Added executable '$BASENAME' to lakefile.lean"
fi

echo "Building $BASENAME..."
lake build "$BASENAME"

if [ $? -eq 0 ]; then
    echo "Running $BASENAME..."
    lake exe "$BASENAME"
else
    echo "Build failed!"
    exit 1
fi