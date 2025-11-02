import Mathlib

/-
# Basic Mathematical Analysis in Lean 4

This file contains definitions and proofs related to sequence convergence,
specifically the squeeze theorem for sequences.
-/

/--
Definition of sequence convergence.

A sequence `a : ℕ → ℝ` converges to a limit `L : ℝ` if for every positive `ε`,
there exists a natural number `N` such that for all `n > N`, the absolute value
of `a n - L` is less than `ε`.

This is the standard ε-N definition of convergence.
-/
def seq_converges_to (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n > N, |a n - L| < ε

/--
The Squeeze Theorem (also known as the Sandwich Theorem or Pinching Theorem).

If we have three sequences `a`, `b`, `c : ℕ → ℝ` such that:
- `a ≤ b ≤ c` (pointwise ordering)
- `a` converges to `L`
- `c` converges to `L`

Then `b` also converges to `L`.

**Proof strategy:**
1. Given `ε > 0`, use convergence of `a` and `c` to find witnesses `N₁` and `N₂`
2. Use `max N₁ N₂` as the witness for `b`
3. For `n > max N₁ N₂`, use the ordering `a n ≤ b n ≤ c n` and the bounds
   from `a` and `c` to show `|b n - L| < ε`
-/
theorem squeeze_theorem (a b c : ℕ → ℝ) (L : ℝ)
  -- Assumptions: ordering and convergence
  (a_le_b : a ≤ b) (b_le_c : b ≤ c)
  (a_to_L : seq_converges_to a L)
  (c_to_L : seq_converges_to c L) :
  -- Conclusion: b also converges to L
  seq_converges_to b L := by
  -- Unfold the definition of convergence
  unfold seq_converges_to
  unfold seq_converges_to at a_to_L
  unfold seq_converges_to at c_to_L

  -- Given ε > 0, we need to find N such that for n > N, |b n - L| < ε
  intro ε ε_pos

  -- Step 1: Get witnesses from convergence of a and c
  -- Since a converges to L, there exists N₁ such that |a n - L| < ε for n > N₁
  obtain ⟨N₁, hN₁⟩ := a_to_L ε ε_pos
  -- Since c converges to L, there exists N₂ such that |c n - L| < ε for n > N₂
  obtain ⟨N₂, hN₂⟩ := c_to_L ε ε_pos

  -- Step 2: Use the maximum of the two witnesses
  -- For n > max(N₁, N₂), both conditions from a and c will hold
  use max N₁ N₂
  intro n hn

  -- Step 3: Show that n > max(N₁, N₂) implies n > N₁ and n > N₂
  have hn₁ : n > N₁ := by omega
  have hn₂ : n > N₂ := by omega

  -- Step 4: Apply convergence bounds for a and c
  have ha : |a n - L| < ε := hN₁ n hn₁
  have hc : |c n - L| < ε := hN₂ n hn₂

  -- Step 5: Extract the ordering constraints at index n
  have hab : a n ≤ b n := a_le_b n
  have hbc : b n ≤ c n := b_le_c n

  -- Step 6: Convert absolute value inequalities to double inequalities
  -- |x| < ε means -ε < x < ε
  have ha_bounds : -ε < a n - L ∧ a n - L < ε := abs_lt.mp ha
  have hc_bounds : -ε < c n - L ∧ c n - L < ε := abs_lt.mp hc

  -- Step 7: Use ordering to bound b n - L
  -- Since a n ≤ b n ≤ c n, we have a n - L ≤ b n - L ≤ c n - L
  have : a n - L ≤ b n - L := by linarith [hab]
  have : b n - L ≤ c n - L := by linarith [hbc]

  -- Step 8: Combine all bounds
  -- We have: -ε < a n - L ≤ b n - L ≤ c n - L < ε
  -- This gives: -ε < b n - L < ε
  have h_left : -ε < b n - L := by linarith
  have h_right : b n - L < ε := by linarith

  -- Step 9: Convert back to absolute value form
  -- -ε < b n - L < ε means |b n - L| < ε
  exact abs_lt.mpr ⟨h_left, h_right⟩
