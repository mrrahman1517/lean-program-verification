def m: Nat := 1
#check (m)
#eval m

def n: Nat := 0
def b1: Bool := true

#check n + 0

/-comment-/

#check Nat →  Nat
#check Prod Nat  Nat

-- Cartesian product type example
#check Nat × Nat
#check (Prod Nat Nat)  -- or equivalently, Nat × Nat
#check Nat.succ
#check (0,1)
#check Nat.add

#check (2,7).fst
#check (2,7).2

#check Nat
#check Bool

def α : Type := Nat
def β : Type := Bool
def F : Type → Type := List
def G : Type → Type → Type := Prod
def G1 : Type →  Type → Type := Prod

#check α
#check β
#check F
#check List
#check F Nat
#check G Nat Nat

#check Type
#check Type 1
#check Type 2
#check Type 3
#check Type 4
#check Type 5
