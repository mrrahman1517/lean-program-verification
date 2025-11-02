/-!
# Introduction to Lean Programming and Proofs

This file contains basic examples and exercises to introduce fundamental concepts in Lean 4:

## Contents
1. Basic theorem proving with `rfl` and `rw`
2. Type checking with `#check`
3. Expression evaluation with `#eval`
4. Function definitions (both named and lambda functions)
5. Higher-order functions
6. Conditional expressions and boolean logic
7. List operations and concatenation
8. Namespaces and scope management
9. String operations and inspection
10. Pattern matching and function definitions
11. Higher-order functions with default parameters
12. List operations and algorithms (quicksort implementation)
13. Algorithm testing and verification

This serves as a comprehensive introduction to Lean's syntax and capabilities,
covering everything from basic proofs to advanced algorithm implementation.
-/

-- ========================================
-- SECTION 1: Basic Theorem Proving
-- ========================================

/-- A simple theorem demonstrating reflexivity.
Place your cursor after 'by' to see the goal in InfoView: ⊢ 2 + 2 = 4
-/
theorem simple_example : 2 + 2 = 4 := by
  -- The goal is automatically solved by reflexivity
  rfl

/-- Demonstrates commutativity of addition using a rewrite.
Place cursor after 'by' to see the goal: ⊢ a + b = b + a
-/
theorem add_comm (a b : Nat) : a + b = b + a := by
  -- Rewrite using the built-in commutativity theorem
  rw [Nat.add_comm]

-- ========================================
-- SECTION 2: Type Checking and Inspection
-- ========================================

-- Check types of basic Lean constructs
#check Nat              -- Natural numbers type
#check List             -- List type constructor
#check (fun x => x + 1) -- Function type: Nat → Nat

-- ========================================
-- SECTION 3: Expression Evaluation
-- ========================================

-- Basic arithmetic
#eval 2 + 3            -- Result: 5
#eval [1, 2, 3].length -- Result: 3
#eval 1 + 3            -- Result: 4

-- ========================================
-- SECTION 4: Function Definitions
-- ========================================

-- Lambda functions (anonymous functions)
#check fun n : Nat => n + 1  -- Type: Nat → Nat
#eval (fun n: Nat => n + 1) 33  -- Apply lambda to 33, result: 34

-- Alternative lambda syntax
#eval (λ x => 2 * x) 126  -- Result: 252

-- Named function definition
def mystery x := 2 * x
#eval mystery 222  -- Result: 444

-- ========================================
-- SECTION 5: Higher-Order Functions
-- ========================================

/-- A higher-order function that applies a function twice.
Takes a value x and a function f, returns f(f(x))
-/
def square (x: Nat) (f : Nat → Nat) := f (f x)
#eval square 5 (λ x => 3 * x)  -- Result: 3 * (3 * 5) = 45

-- ========================================
-- SECTION 6: Boolean Logic and Conditionals
-- ========================================

-- Boolean comparisons
#eval 1 + 1 == 3  -- Result: false
#eval if 1 + 1 == 2 then "True" else "False"      -- Result: "True"
#eval if 1 + 2 == 33 then "True" else "False"     -- Result: "False"

-- ========================================
-- SECTION 7: List Operations
-- ========================================

-- List concatenation
#eval ["Penrose"] ++ ["Milner", "Dirac"]  -- Result: ["Penrose", "Milner", "Dirac"]

-- ========================================
-- SECTION 8: Namespaces and Scope
-- ========================================

-- Demonstration of namespace usage.
-- Namespaces help organize code and prevent naming conflicts.
namespace Mystery
  -- A function that appends "..." to any string
  def f x := x ++ "..."
end Mystery

-- Using qualified name
#eval Mystery.f "Ping"  -- Result: "Ping..."

-- Opening namespace to use unqualified names
open Mystery
#eval f "Pong"  -- Result: "Pong..."

#check f  -- Shows the type of the opened function

-- ========================================
-- SECTION 9: String Operations and Inspection
-- ========================================

-- Basic type checking for strings
#check String      -- The String type
#check Type        -- Type of types
#check Type 1      -- Higher universe type

-- String function inspection
#check String.length        -- Type: String → Nat
#print String.length        -- Shows the definition
#check @String.length       -- Explicit argument version

-- String length examples
#eval "hello".length  -- Result: 5
#eval "".length       -- Result: 0 (empty string)

-- Other string operations
#print String.append         -- Shows definition of string concatenation
#check String.toList         -- Convert string to list of characters

-- Namespace inspection
#check String  -- The String type and its namespace

-- Note: Uncomment the following line to see all String definitions
-- #print String

-- ========================================
-- SECTION 10: Pattern Matching and Function Definitions
-- ========================================

/-- Function using if-then-else conditional logic.
Demonstrates simple conditional branching based on numeric comparison.
-/
def f1 x :=
  if x < 10 then "small"
  else "large"

-- Test the conditional function
#eval f1 5   -- Result: "small" (5 < 10)
#eval f1 55  -- Result: "large" (55 >= 10)

/-- Function using pattern matching with explicit match expression.
Shows how to handle multiple specific cases with pattern matching.
-/
def f2 (n: Nat) : String :=
  match n with
  | 0 => "small"        -- Exact match for 0
  | 1 => "small"        -- Exact match for 1
  | _ => "large"        -- Wildcard for all other cases
  
-- Test pattern matching
#eval f2 2  -- Result: "large" (matches wildcard)
#eval f2 1  -- Result: "small" (exact match)

/-- Function using direct pattern matching syntax.
Alternative syntax for pattern matching - more concise than match expressions.
-/
def f3 : Nat → String
  | 0 => "small"        -- Direct pattern syntax
  | 1 => "small"        
  | _ => "big"          -- Note: different return value for demonstration

-- Test direct pattern matching
#eval f3 33  -- Result: "big"

-- ========================================
-- SECTION 11: Higher-Order Functions with Default Parameters
-- ========================================

/-- Higher-order function with default parameter.
Demonstrates default function parameters and function composition.
The default operation is squaring (λ x => x * x).
-/
def squarev2 (x: Nat) (op : Nat → Nat := λ x => x * x) :=
  op (op x)  -- Apply the operation twice: op(op(x))

-- Test with default operation (squaring)
#eval squarev2 (5)           -- Result: ((5²)²) = (25)² = 625

-- Test with custom operation (doubling)
#eval squarev2 (6) λ x => x + x  -- Result: (6+6)+(6+6) = 12+12 = 24

-- ========================================
-- SECTION 12: List Operations and Algorithms
-- ========================================

-- Check the type of List.map (higher-order function for lists)
#check List.map  -- Type: {α β : Type u_1} → (α → β) → List α → List β

/-- Quicksort algorithm implementation in Lean.
Sorts a list of natural numbers in ascending order using the divide-and-conquer approach.

Algorithm steps:
1. Base case: empty list is already sorted
2. Choose first element as pivot
3. Partition remaining elements into smaller (≤ pivot) and larger (> pivot)
4. Recursively sort both partitions
5. Concatenate: sorted_smaller ++ [pivot] ++ sorted_larger

We use `partial` to bypass termination checking for educational simplicity.
-/
partial def quicksort (xs : List Nat) : List Nat :=
  match xs with
  | [] => []  -- Empty list is already sorted
  | pivot :: rest =>
    let smaller := rest.filter (· ≤ pivot)     -- Elements ≤ pivot
    let larger := rest.filter (· > pivot)      -- Elements > pivot
    quicksort smaller ++ [pivot] ++ quicksort larger

-- ========================================
-- SECTION 13: Algorithm Testing and Verification
-- ========================================

-- Test the quicksort function with various inputs
#eval quicksort [3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5]  -- Result: [1, 1, 2, 3, 3, 4, 5, 5, 5, 6, 9]
#eval quicksort [5, 2, 8, 1, 9]                      -- Result: [1, 2, 5, 8, 9]
#eval quicksort []                                    -- Result: [] (empty list)
#eval quicksort [42]                                  -- Result: [42] (single element)
