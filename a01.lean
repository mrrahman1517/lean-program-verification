/-!
# Assignment 1: Basic Functions and Collatz Conjecture

This is the first assignment. These assignments are intended for practice and
should be completed after each lecture to help with understanding.

## Contents
1. Cube function - calculates x³
2. Collatz conjecture implementation with various utilities
-/

/-- Q1: Define a function that calculates the cube of an integer.
Use `sorry` to mark a value that you will fill in later.

The cube function multiplies a number by itself three times: x³ = x × x × x
-/
def cube (x : Nat) := x * x * x

-- Test: cube of 5 should output 125
#eval cube 5

/-- Q2: Define the step function in Collatz's conjecture.

The Collatz conjecture (also known as the 3n+1 problem) states:
- If x is even: divide by 2
- If x is odd: multiply by 3 and add 1

The conjecture is that starting from any positive integer,
this process will eventually reach 1.

Hint: The remainder function is `%`. (e.g. `5 % 2 = 1`)
-/
def collatz (x : Nat) : Nat :=
  if x % 2 = 0 then x / 2 else 3 * x + 1

-- Test: collatz(6) = 3, collatz(3) = 10
#eval collatz 6
#eval collatz 3

/-- Apply the Collatz function repeatedly until reaching 1.

This function keeps applying the Collatz step until the sequence reaches 1.
Since the Collatz conjecture is unproven, we use a maximum step limit
to ensure termination in Lean.

Parameters:
- x: starting number
- maxSteps: maximum iterations (default 1000) to prevent infinite loops
-/
def collatzSequence (x : Nat) (maxSteps : Nat := 1000) : Nat :=
  if maxSteps = 0 then x  -- safety: return current value if we hit max steps
  else if x = 1 then 1
  else collatzSequence (collatz x) (maxSteps - 1)

-- Test convergence for different starting values
#eval collatzSequence 6   -- Should reach 1
#eval collatzSequence 7   -- Should reach 1
#eval collatzSequence 10  -- Should reach 1

/-- Count the number of steps needed to reach 1 in the Collatz sequence.

This function counts how many iterations of the Collatz function
are needed before reaching 1.

Returns:
- The number of steps to reach 1
- maxSteps if the limit is reached (indicating possible non-convergence)
-/
def collatzSteps (x : Nat) (maxSteps : Nat := 1000) : Nat :=
  if maxSteps = 0 then maxSteps  -- return max steps if we hit the limit
  else if x = 1 then 0
  else 1 + collatzSteps (collatz x) (maxSteps - 1)

-- Test step counting for various starting values
#eval collatzSteps 6   -- 6 → 3 → 10 → 5 → 16 → 8 → 4 → 2 → 1 (8 steps)
#eval collatzSteps 7   -- Longer sequence
#eval collatzSteps 10  -- 10 → 5 → 16 → 8 → 4 → 2 → 1 (6 steps)

/-- Generate the complete Collatz sequence as a list.

This function returns the entire sequence from the starting number
down to 1, showing every intermediate value.

This is useful for visualizing the behavior of the Collatz conjecture
and seeing the "path" taken to reach 1.
-/
def collatzList (x : Nat) (maxSteps : Nat := 1000) : List Nat :=
  if maxSteps = 0 then [x]  -- safety: return current value if we hit max steps
  else if x = 1 then [1]
  else x :: collatzList (collatz x) (maxSteps - 1)

-- Display complete sequences for various starting values
#eval collatzList 6    -- [6, 3, 10, 5, 16, 8, 4, 2, 1]
#eval collatzList 7    -- Shows the famous long sequence starting from 7
#eval collatzList 10   -- [10, 5, 16, 8, 4, 2, 1]
#eval collatzList 5    -- [5, 16, 8, 4, 2, 1]
#eval collatzList 1    -- [1] (trivial case)
#eval collatzList 411  -- A longer example to test the algorithm
