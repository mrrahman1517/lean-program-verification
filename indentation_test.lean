-- Example demonstrating auto-indentation in Lean
def example_function (n : Nat) : Nat :=
  if n = 0 then
    1
  else
    n * example_function (n - 1)

def main : IO Unit := do
  IO.println "Testing auto-indentation:"
  let numbers := [1, 2, 3, 4, 5]
  for num in numbers do
    let result := example_function num
    IO.println s!"factorial({num}) = {result}"

  -- Match expression example
  let test_value := 3
  match test_value with
  | 0 => IO.println "zero"
  | 1 => IO.println "one"
  | n => IO.println s!"other: {n}"

-- Theorem example with structured proof
theorem simple_theorem (n : Nat) : n + 0 = n := by
  rw [Nat.add_zero]


def test : IO Unit := do
  -- This line should be indented with 2 spaces (appears as tab-width)
  let x := 5
  -- This line should also be indented
  IO.println s!"Value: {x}"

-- Try this: place cursor after 'do' above and press Enter
-- The cursor should automatically indent with 2 spaces

def another_test : IO Unit := do
  -- Test auto-indentation here
  IO.println "Hello"
  -- Press Enter at end of this line and type something
  let numbers := [1, 2, 3]
  for n in numbers do
    IO.println s!"Number: {n}"
