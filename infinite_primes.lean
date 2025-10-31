-- Import basic prime number facts and factorials from Mathlib
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Factorial

-- Open the Nat namespace for easier access to natural number functions
open Nat


-- Theorem: There are infinitely many primes (Euclid's proof)
-- For any natural number N, there exists a prime p > N
theorem infinite_primes : ∀ N : ℕ, ∃ p : ℕ, p > N ∧ Nat.Prime p := by
  intro N
  -- Let M = N! + 1
  let M := Nat.factorial N + 1

  -- Let p be the minimal prime factor of M
  let p := M.minFac

  -- Show M ≠ 1 (so minFac is prime)
  have M_ne_one : M ≠ 1 := by
    have : 0 < Nat.factorial N := Nat.factorial_pos N
    omega
  -- p is prime
  have pp : Nat.Prime p := Nat.minFac_prime M_ne_one
  use p
  constructor
  · -- Show p > N
    by_contra h
    -- If p ≤ N, then p divides N!
    have : p ≤ N := by omega
    have hfact : p ∣ Nat.factorial N := pp.dvd_factorial.mpr this
    -- p divides M = N! + 1
    have hM : p ∣ M := Nat.minFac_dvd M
    -- So p divides (N! + 1) - N! = 1
    -- (handled below)
    -- Show N! ≤ M
    have hle : Nat.factorial N ≤ M := by
      dsimp [M]
      omega
    -- p ∣ (M - N!)
    have hdiv : p ∣ (M - Nat.factorial N) := by
      apply Nat.dvd_sub
      · exact hM
      · exact hfact

    -- M - N! = 1
    have hsub : M - Nat.factorial N = 1 := by
      dsimp [M]
      omega
    rw [hsub] at hdiv
    have : p ∣ 1 := hdiv
    -- But no prime divides 1
    have : ¬p ∣ 1 := Nat.Prime.not_dvd_one pp
    contradiction
  · -- Show p is prime (already shown)
    exact pp


-- Main function for IO demonstration
def main : IO Unit := do
  IO.println "Infinite Primes File"
  IO.println "Mathlib prime number definitions loaded successfully!"
