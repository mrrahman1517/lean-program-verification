#!/bin/bash

# Simple function to add a new Lean executable to lakefile.lean
# Usage: ./add_executable.sh filename

if [ $# -eq 0 ]; then
    echo "Usage: $0 <filename_without_extension>"
    echo "Example: $0 myprogram"
    echo "This will add an executable for myprogram.lean"
    exit 1
fi

FILENAME="$1"

# Add the executable entry before the require mathlib line
echo "
lean_exe «$FILENAME» where
  root := \`$FILENAME" >> temp_exe.txt

# Insert into lakefile before the require line
head -n -3 lakefile.lean > temp_lakefile.txt
cat temp_exe.txt >> temp_lakefile.txt
tail -n 3 lakefile.lean >> temp_lakefile.txt
mv temp_lakefile.txt lakefile.lean
rm temp_exe.txt

echo "Added executable '$FILENAME' to lakefile.lean"
echo "Now you can run: lake build $FILENAME && lake exe $FILENAME"