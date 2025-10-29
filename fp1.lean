-- Basic arithmetic functions
def add1 (n : Nat) : Nat := n + 1

#eval add1 7

def add2 (n : Nat)(m : Nat) := n + m

#eval add2 7 2

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
#eval fact4 5  -- Expected: 120
-- ▼ EVAL OUTPUT: 120

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
#eval fib 0   -- Expected: 0
-- ▼ EVAL OUTPUT: 0

#eval fib 1   -- Expected: 1
-- ▼ EVAL OUTPUT: 1

#eval fib 2   -- Expected: 1
-- ▼ EVAL OUTPUT: 1

#eval fib 5   -- Expected: 5
-- ▼ EVAL OUTPUT: 5

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
#eval sum_list []           -- Expected: 0
-- ▼ EVAL OUTPUT: 0

#eval sum_list [1, 2, 3, 4] -- Expected: 10
-- ▼ EVAL OUTPUT: 10

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
#eval list_length ([] : List Nat)        -- Expected: 0
-- ▼ EVAL OUTPUT: 0

#eval list_length [1, 2, 3]              -- Expected: 3
-- ▼ EVAL OUTPUT: 3
#eval list_length ["a", "b", "c", "d"]   -- Expected: 4

-- =============================================================================
-- OPTION TYPE PATTERN MATCHING: Handling Maybe Values
-- =============================================================================

-- Safe division that returns Option (maybe a result)
def safe_div (a b : Nat) : Option Nat :=
    match b with
    | 0 => none                 -- Division by zero returns none
    | _ => some (a / b)         -- Valid division returns some result

#eval safe_div 10 2  -- Expected: some 5
-- ▼ EVAL OUTPUT: some 5

#eval safe_div 10 0  -- Expected: none
-- ▼ EVAL OUTPUT: none

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
#eval get_or_default (some 42) 0    -- Expected: 42
-- ▼ EVAL OUTPUT: 42

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

#eval not1 false  -- Expected: true
#eval not1 true   -- Expected: false

-- AND FUNCTION: Boolean conjunction using pattern matching
-- Returns true only if both inputs are true; otherwise returns false.
-- If first input is false, returns false immediately (short-circuit).
def and1 (b1 : Bool) (b2 : Bool) : Bool :=
    match b1 with
    | false => false
    | true => b2

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

#eval fact1 5

#eval String.append "Who is the greatest theoretical physicist, it is " (if 1 > 2 then "Fermi" else "Dirac" )

#eval String.append "Who is the greatest theoretical physicist, it is " (if 10 > 2 then "Fermi" else "Dirac" )

#eval String.append "it is" "it"

#eval 42 +19

#eval String.append "A" (String.append "B" "C")

#eval String.append (String.append "A" "B") "C"

#eval if 3 == 3 then 5 else 7

#eval if 3 == 4 then "equal" else "not equal"

#eval (1 + 2 : Nat)

--#eval (1 + "2") -- does not compile

#eval (1 -2 : Nat) -- Nat

#eval (1 - 2 : Int)

#check (1 - 2) -- #check allows us to inspect the type of an expression

#eval 12122323232323232323232323323232323 + 34343434343434343434343 + 34343434343434333434343434433

#check 12122323232323232323232323323232323 + 34343434343434343434343 + 34343434343434333434343434433

def hello (person : String) : String := String.append "hello " person

#check hello
#eval hello "Witten"
#eval hello "Penrose"
#eval hello "Weinberg"

def add1v2 (n : Nat) : Nat := n + 1
#eval add1v2 37

def maximum (n : Nat) (m : Nat) : Nat :=
    if n < m then m
    else n

#check maximum
#check (maximum)
#eval maximum 45 78

def threeSum (n1: Nat) (n2: Nat) (n3: Nat): Nat :=
    n1 + n2 + n3

#check (threeSum)
#check (threeSum 1)
#check (threeSum 1 2)
#check (threeSum 1 2 3)

def spaceBetween (first : String) (second: String) : String :=
    String.append first (String.append " " second)

#check spaceBetween
#eval spaceBetween "Paul" "Dirac"

#eval maximum (2 +45) (7+90)

def joinStringsWith (first: String) (second: String) (third: String): String :=
    String.append second (String.append first third)

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
