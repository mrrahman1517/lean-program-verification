#!/bin/bash

# Create a new Lean file with basic template and run it
# Usage: ./new_lean.sh filename

if [ $# -eq 0 ]; then
    echo "Usage: $0 <filename_without_extension>"
    echo "Example: $0 myprogram"
    exit 1
fi

FILENAME="$1"

cat > "$FILENAME.lean" << 'EOF'
-- New Lean program
def main : IO Unit := do
  IO.println "Hello from a new Lean program!"
  -- Add your code here
EOF

echo "Created $FILENAME.lean"
echo "Running it..."
lean --run "$FILENAME.lean"