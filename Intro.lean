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
7. Namespaces and scope management
8. String operations and inspection

This serves as a gentle introduction to Lean's syntax and capabilities.
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