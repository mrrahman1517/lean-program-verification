-- =============================================================================
-- STRUCTURE EXAMPLE: 2D Point with Float Coordinates
-- =============================================================================

-- Define a structure for a 2D point with floating-point coordinates
structure Pointv2 where
    x : Float
    y : Float

-- Example: create a Pointv2 value representing the origin
def origin2D : Pointv2 := {x := 0.0, y := 0.0}
#check origin2D
#eval origin2D
-- Basic arithmetic functions
-- add1: Increments a natural number by 1
def add1 (n : Nat) : Nat := n + 1

-- Example: increment 7 by 1
#eval add1 7

-- add2: Adds two natural numbers
def add2 (n : Nat)(m : Nat) := n + m

-- Example: add 7 and 2
#eval add2 7 2

-- Direct evaluation of an arithmetic expression
#eval 1 + 2

-- =============================================================================
-- FACTORIAL FUNCTIONS: Multiple Pattern Matching Styles
-- =============================================================================

-- Style 1: Basic pattern matching with k + 1 decomposition
-- This is the most common and idiomatic way in Lean 4
def fact1 (n : Nat) : Nat :=
    match n with
    | 0 => 1                    -- Base case: factorial of 0 is 1
    | k + 1 => (k + 1) * fact1 k -- Recursive case: n! = n * (n-1)!

-- Test fact1 with various inputs
#eval fact1 5  -- Expected: 120
#eval fact1 0  -- Expected: 1
#eval fact1 1  -- Expected: 1
#eval fact1 6  -- Expected: 720

-- Style 2: Using Nat.succ (successor function)
-- More explicit about the natural number structure
def fact2 (n : Nat) : Nat :=
    match n with
    | Nat.zero => 1             -- Base case using Nat.zero
    | Nat.succ k => (k + 1) * fact2 k -- Recursive case using Nat.succ

-- Test fact2 with various inputs
#eval fact2 5  -- Expected: 120
#eval fact2 0  -- Expected: 1
#eval fact2 4  -- Expected: 24

-- Style 3: With explicit small cases
-- Handles 0 and 1 explicitly, then general case
def fact3 (n : Nat) : Nat :=
    match n with
    | 0 => 1                    -- factorial(0) = 1
    | 1 => 1                    -- factorial(1) = 1
    | n + 1 => (n + 1) * fact3 n -- General recursive case

-- Test fact3 with various inputs
#eval fact3 5  -- Expected: 120
#eval fact3 1  -- Expected: 1
#eval fact3 2  -- Expected: 2

-- Style 4: Pattern matching with guards (conditional logic)
-- Uses if-then-else within the pattern match
def fact4 (n : Nat) : Nat :=
    match n with
    | 0 => 1                    -- Base case
    | m => if m > 0 then
             m * fact4 (m - 1)  -- Recursive multiplication
           else
             1                  -- Fallback (though unreachable for Nat)

-- ═══════════════════════════════════════════════════════════════════════════════
-- 🧮 FACTORIAL EVALUATION TESTS
-- ═══════════════════════════════════════════════════════════════════════════════
-- Test fact4 with various inputs
#eval fact4 5  -- Expected: 120
-- ▼ EVAL OUTPUT: 120
-- Example: fact4 with input 3
#eval fact4 3  -- Expected: 6
-- ▼ EVAL OUTPUT: 6

-- =============================================================================
-- FIBONACCI SEQUENCE: Demonstrating Multiple Pattern Cases
-- =============================================================================

-- Fibonacci using pattern matching with multiple base cases
def fib (n : Nat) : Nat :=
    match n with
    | 0 => 0                    -- fib(0) = 0
    | 1 => 1                    -- fib(1) = 1
    | k + 2 => fib (k + 1) + fib k -- fib(n) = fib(n-1) + fib(n-2)

-- ═══════════════════════════════════════════════════════════════════════════════
-- 🔢 FIBONACCI EVALUATION TESTS
-- ═══════════════════════════════════════════════════════════════════════════════
-- Test Fibonacci with various inputs
#eval fib 0   -- Expected: 0
-- ▼ EVAL OUTPUT: 0
#eval fib 1   -- Expected: 1
-- ▼ EVAL OUTPUT: 1
-- Example: fib with input 2
#eval fib 2   -- Expected: 1
-- ▼ EVAL OUTPUT: 1
-- Example: fib with input 5
#eval fib 5   -- Expected: 5
-- ▼ EVAL OUTPUT: 5
-- Example: fib with input 10
#eval fib 10  -- Expected: 55
-- ▼ EVAL OUTPUT: 55

-- =============================================================================
-- LIST PATTERN MATCHING: Working with Data Structures
-- =============================================================================

-- Sum all elements in a list using pattern matching
def sum_list (lst : List Nat) : Nat :=
    match lst with
    | [] => 0                   -- Empty list sums to 0
    | head :: tail => head + sum_list tail -- Add head to sum of tail

-- ═══════════════════════════════════════════════════════════════════════════════
-- 📋 LIST SUM EVALUATION TESTS
-- ═══════════════════════════════════════════════════════════════════════════════
-- Test sum_list with empty and non-empty lists
#eval sum_list []           -- Expected: 0
-- ▼ EVAL OUTPUT: 0
#eval sum_list [1, 2, 3, 4] -- Expected: 10
-- ▼ EVAL OUTPUT: 10
-- Example: sum_list with a single-element list
#eval sum_list [5]          -- Expected: 5
-- ▼ EVAL OUTPUT: 5

-- Get length of a list using pattern matching
def list_length (lst : List α) : Nat :=
    match lst with
    | [] => 0                   -- Empty list has length 0
    | _ :: tail => 1 + list_length tail -- 1 + length of remaining

-- ═══════════════════════════════════════════════════════════════════════════════
-- 📏 LIST LENGTH EVALUATION TESTS
-- ═══════════════════════════════════════════════════════════════════════════════
-- Test list_length with lists of different types
#eval list_length ([] : List Nat)        -- Expected: 0
-- ▼ EVAL OUTPUT: 0
#eval list_length [1, 2, 3]              -- Expected: 3
-- ▼ EVAL OUTPUT: 3
-- Example: list_length with a string list
#eval list_length ["a", "b", "c", "d"]   -- Expected: 4

-- =============================================================================
-- OPTION TYPE PATTERN MATCHING: Handling Maybe Values
-- =============================================================================

-- Safe division that returns Option (maybe a result)
def safe_div (a b : Nat) : Option Nat :=
    match b with
    | 0 => none                 -- Division by zero returns none
    | _ => some (a / b)         -- Valid division returns some result

-- Test safe_div with valid and invalid divisors
#eval safe_div 10 2  -- Expected: some 5
-- ▼ EVAL OUTPUT: some 5
#eval safe_div 10 0  -- Expected: none
-- ▼ EVAL OUTPUT: none
-- Example: safe_div with 7 divided by 3
#eval safe_div 7 3   -- Expected: some 2
-- ▼ EVAL OUTPUT: some 2

-- Extract value from Option with default
def get_or_default (opt : Option Nat) (default : Nat) : Nat :=
    match opt with
    | none => default           -- Use default if no value
    | some value => value       -- Extract the value if present

-- ═══════════════════════════════════════════════════════════════════════════════
-- 🔍 OPTION EXTRACTION EVALUATION TESTS
-- ═══════════════════════════════════════════════════════════════════════════════
-- Test get_or_default with present and missing values
-- Example: get_or_default with present value
#eval get_or_default (some 42) 0    -- Expected: 42
-- ▼ EVAL OUTPUT: 42
-- Example: get_or_default with missing value
#eval get_or_default none 99        -- Expected: 99
-- ▼ EVAL OUTPUT: 99

-- =============================================================================
-- BOOLEAN PATTERN MATCHING: Control Flow
-- =============================================================================

-- Convert boolean to natural number using pattern matching
def bool_to_nat (b : Bool) : Nat :=
    match b with
    | true => 1                 -- true becomes 1
    | false => 0                -- false becomes 0

-- ═══════════════════════════════════════════════════════════════════════════════
-- ✅ BOOLEAN CONVERSION EVALUATION TESTS
-- ═══════════════════════════════════════════════════════════════════════════════
-- Test bool_to_nat with both boolean values
#eval bool_to_nat true   -- Expected: 1
-- ▼ EVAL OUTPUT: 1
#eval bool_to_nat false  -- Expected: 0
-- ▼ EVAL OUTPUT: 0




-- NOT FUNCTION: Boolean negation using pattern matching
-- Takes a boolean value and returns its logical negation.
-- If input is false, returns true; if input is true, returns false.
def not1 (b : Bool) : Bool :=
    match b with
    | false => true   -- Negation of false is true
    | true => false   -- Negation of true is false

-- Test not1 (boolean negation)
-- Example: not1 with false and true
#eval not1 false  -- Expected: true
#eval not1 true   -- Expected: false

-- AND FUNCTION: Boolean conjunction using pattern matching
-- Returns true only if both inputs are true; otherwise returns false.
-- If first input is false, returns false immediately (short-circuit).
def and1 (b1 : Bool) (b2 : Bool) : Bool :=
    match b1 with
    | false => false
    | true => b2

-- Test and1 (boolean conjunction)
-- Example: and1 with all boolean combinations
#eval and1 false false  -- Expected: false
#eval and1 false true   -- Expected: false
#eval and1 true false   -- Expected: false
#eval and1 true true    -- Expected: true

-- OR FUNCTION: Boolean disjunction using pattern matching
-- Returns true if at least one input is true; otherwise returns false.
-- If first input is true, returns true immediately (short-circuit).
def or1 (b1: Bool) (b2: Bool) : Bool :=
    match b1 with
    | false => b2   -- If first is false, result depends on second
    | true => true  -- If first is true, always true

-- Test or1 (boolean disjunction)
-- Example: or1 with all boolean combinations
#eval or1 false false  -- Expected: false
#eval or1 false true   -- Expected: true
#eval or1 true false   -- Expected: true
#eval or1 true true    -- Expected: true

-- =============================================================================
-- MAIN FUNCTION: Testing All Definitions
-- =============================================================================

def main : IO Unit := do
    IO.println "=== Pattern Matching Examples in Lean 4 ==="
    IO.println ""

    -- Test factorial functions
    IO.println "Factorial Functions:"
    IO.println s!"fact1(5) = {fact1 5}"
    IO.println s!"fact2(5) = {fact2 5}"
    IO.println s!"fact3(5) = {fact3 5}"
    IO.println s!"fact4(5) = {fact4 5}"
    IO.println ""

    -- Test Fibonacci
    IO.println "Fibonacci Sequence:"
    IO.println s!"fib(10) = {fib 10}"
    IO.println ""

    -- Test list operations
    IO.println "List Operations:"
    IO.println s!"sum_list([1,2,3,4]) = {sum_list [1,2,3,4]}"
    IO.println s!"list_length([1,2,3]) = {list_length [1,2,3]}"
    IO.println ""

    -- Test safe division
    IO.println "Safe Division:"
    IO.println s!"safe_div(10,2) = {safe_div 10 2}"
    IO.println s!"safe_div(10,0) = {safe_div 10 0}"
    IO.println ""

    -- Test boolean ops
    IO.println "boolean logic:"
    IO.println s!"and1(false, false) = {and1 false false}"
    IO.println s!"and1(false, true) = {and1 false true}"
    IO.println s!"and1(true, false) = {and1 true false}"
    IO.println s!"and1(true, true) = {and1 true true}"

    IO.println s!"or1(false, false) = {or1 false false}"
    IO.println s!"or1(false, true) = {or1 false true}"
    IO.println s!"or1(true, false) = {or1 true false}"
    IO.println s!"or1(true, true) = {or1 true true}"

    IO.println s!"not1(false) = {not1 false}"
    IO.println s!"not1(true) = {not1 true}"



    IO.println "All pattern matching examples completed!"

-- Redundant test for fact1 (already tested above)
#eval fact1 5

-- String concatenation with conditional
-- Example: conditional string append (false branch)
#eval String.append "Who is the greatest theoretical physicist, it is " (if 1 > 2 then "Fermi" else "Dirac" )

-- String concatenation with conditional (true branch)
-- Example: conditional string append (true branch)
#eval String.append "Who is the greatest theoretical physicist, it is " (if 10 > 2 then "Fermi" else "Dirac" )

-- Simple string concatenation
#eval String.append "it is" "it"

-- Simple arithmetic
#eval 42 +19

-- Nested string concatenation
#eval String.append "A" (String.append "B" "C")

-- Nested string concatenation (different grouping)
#eval String.append (String.append "A" "B") "C"

-- Conditional expression (true branch)
#eval if 3 == 3 then 5 else 7

-- Conditional expression (false branch)
#eval if 3 == 4 then "equal" else "not equal"

-- Explicit type annotation for arithmetic
#eval (1 + 2 : Nat)

--#eval (1 + "2") -- does not compile

-- Subtraction with Nat (result is 0 if negative)
-- Example: subtraction with Nat (result is 0 if negative)
#eval (1 -2 : Nat) -- Nat

-- Subtraction with Int (can be negative)
-- Example: subtraction with Int (can be negative)
#eval (1 - 2 : Int)

-- #check allows us to inspect the type of an expression
#check (1 - 2)

-- Large integer addition
#eval 12122323232323232323232323323232323 + 34343434343434343434343 + 34343434343434333434343434433

-- #check for large integer addition
#check 12122323232323232323232323323232323 + 34343434343434343434343 + 34343434343434333434343434433

-- hello: Greets a person by name
def hello (person : String) : String := String.append "hello " person

-- #check and #eval for hello
#check hello
#eval hello "Witten"
#eval hello "Penrose"
#eval hello "Weinberg"

-- add1v2: Another increment function
def add1v2 (n : Nat) : Nat := n + 1
#eval add1v2 37

-- maximum: Returns the larger of two natural numbers
def maximum (n : Nat) (m : Nat) : Nat :=
    if n < m then m
    else n

-- #check and #eval for maximum
#check maximum
#check (maximum)
#eval maximum 45 78

-- threeSum: Sums three natural numbers
def threeSum (n1: Nat) (n2: Nat) (n3: Nat): Nat :=
    n1 + n2 + n3

-- #check for threeSum and partial application
#check (threeSum)
#check (threeSum 1)
#check (threeSum 1 2)
#check (threeSum 1 2 3)

-- spaceBetween: Concatenates two strings with a space in between
def spaceBetween (first : String) (second: String) : String :=
    String.append first (String.append " " second)

-- #check and #eval for spaceBetween
#check spaceBetween
#eval spaceBetween "Paul" "Dirac"

-- Test maximum with arithmetic expressions
#eval maximum (2 +45) (7+90)

-- joinStringsWith: Concatenates three strings in a custom order
def joinStringsWith (first: String) (second: String) (third: String): String :=
    String.append second (String.append first third)

-- #check and #eval for joinStringsWith
#check (joinStringsWith)
#check (joinStringsWith ", ")
#eval joinStringsWith ", " "one" "and another"
#eval joinStringsWith "+" "2" "3"

-- VOLUME FUNCTION: Calculates the volume of a rectangular box (cuboid)
-- Multiplies height, width, and depth to get the total volume
def volume (height: Nat) (width: Nat) (depth: Nat) : Nat := height * width * depth

-- #check shows the type of the function (Nat → Nat → Nat → Nat)
#check (volume)
-- #check shows the type after partially applying one argument (Nat → Nat → Nat)
#check (volume 2)
-- #eval computes the volume for height=2, width=3, depth=4 (should be 24)
#eval (volume 2 3 4)  -- Expected: 24


-- Type alias for String
def Str: Type := String
-- Example string value
def aStr : Str := "curry howard correspondence"
#check (aStr)
#eval aStr



-- Type alias for Nat
def NaturalNumber: Type := Nat
-- Example natural number value
def fortySeven : NaturalNumber := (47: Nat)
#check (fortySeven)
#eval (fortySeven)


-- Abbreviation for Nat
abbrev N : Type := Nat
-- Example value using abbreviation
def two: N := 2
#check(N)
#check N
#check(two)
#eval(two)

-- Example: type check for a float literal
#check (1.2)

def origin : Pointv2 := {x := 0.0, y := 0.0}

-- Structure definition for a 2D point with float coordinates
