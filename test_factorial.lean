def factorial (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

def main : IO Unit := do
  let numbers := [1, 2, 3, 4, 5]
  IO.println "Computing factorials:"
  for n in numbers do
    IO.println s!"factorial({n}) = {factorial n}"
