def factorial (n: Nat) : Nat :=
  -- This line should be auto-indented when you press Enter after ':='
  if n = 0 then
    1
  else
    n * factorial (n - 1)

-- Test this: Place cursor after ':=' on line 1 and press Enter
-- Expected: Cursor should auto-indent to position of this comment

def simple_function : Nat :=
  42

-- Another test case
def test_do_block : IO Unit := do
  -- Should auto-indent after 'do'
  IO.println "Hello"
  let x := 5
  IO.println s!"Value: {x}"

def main : IO Unit := do
  IO.println "Testing indentation..."
  test_do_block
  let result := factorial 5
  IO.println s!"factorial(5) = {result}"