import Quicksortv2.L.Basic

--
--  Quicksort correctness in Lean 4 + mathlib
--
--  This is a verified implementation of quicksort showing:
--  1. Quicksort produces a permutation of the input
--  2. Quicksort produces a sorted output
--
--  Requires:
--    - Lean 4
--    - mathlib (e.g., via `lake exe cache get` in a mathlib starter project)
--

import Mathlib.Data.List.Permutation
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Sort

open List

namespace QuicksortVerification

variable {α : Type*} [LinearOrder α] [DecidableRel (· ≤ · : α → α → Prop)]

/-- Standard functional quicksort, pivot = head, two-way partition by (≤ pivot) / (> pivot). -/
def qsort : List α → List α
| []       => []
| (x :: xs) =>
  qsort (xs.filter (· ≤ x)) ++ x :: qsort (xs.filter (· > x))
termination_by l => l.length
decreasing_by
  all_goals
    simp_wf
    exact Nat.lt_succ_of_le (length_filter_le _ _)

/-!
## Helper lemmas about the filtering operation
-/

/-- All elements of `xs.filter (· ≤ x)` are `≤ x`. -/
lemma mem_filter_le {x y : α} {xs : List α} (hy : y ∈ xs.filter (· ≤ x)) : y ≤ x := by
  rw [mem_filter] at hy
  exact decide_eq_true_iff.mp hy.2

/-- All elements of `xs.filter (· > x)` are `> x`. -/
lemma mem_filter_gt {x y : α} {xs : List α} (hy : y ∈ xs.filter (· > x)) : x < y := by
  rw [mem_filter] at hy
  exact decide_eq_true_iff.mp hy.2

/-- The partition covers all elements: every element goes to exactly one side. -/
lemma partition_complete {x y : α} {xs : List α} :
    y ∈ xs ↔ y ∈ xs.filter (· ≤ x) ∨ y ∈ xs.filter (· > x) := by
  constructor
  · intro hy
    by_cases h : y ≤ x
    · left
      rw [mem_filter]
      exact ⟨hy, decide_eq_true_iff.mpr h⟩
    · right
      have : x < y := lt_of_not_ge h
      rw [mem_filter]
      exact ⟨hy, decide_eq_true_iff.mpr this⟩
  · intro h
    cases h with
    | inl h =>
      rw [mem_filter] at h
      exact h.1
    | inr h =>
      rw [mem_filter] at h
      exact h.1

/-!
## Main correctness theorems
-/

/-- Quicksort produces a permutation of the input. -/
theorem qsort_perm (xs : List α) : qsort xs ~ xs := by
  induction xs using qsort.induct with
  | case1 => simp [qsort]
  | case2 x xs ih_l ih_r =>
    simp only [qsort]
    -- We need to show: qsort L ++ x :: qsort R ~ x :: xs
    -- where L = xs.filter (· ≤ x) and R = xs.filter (· > x)
    have perm_l : qsort (xs.filter (· ≤ x)) ~ xs.filter (· ≤ x) := ih_l
    have perm_r : qsort (xs.filter (· > x)) ~ xs.filter (· > x) := ih_r

    -- Show the partition forms a permutation with x
    have partition_perm : xs.filter (· ≤ x) ++ x :: xs.filter (· > x) ~ x :: xs := by
      induction xs with
      | nil => simp
      | cons y ys ih =>
        by_cases h : y ≤ x
        · -- y goes to left partition
          simp [filter_cons_of_pos, h, filter_cons_of_neg, not_lt.mpr h]
          exact Perm.cons y ih
        · -- y goes to right partition
          have hy : x < y := lt_of_not_ge h
          simp [filter_cons_of_neg, h, filter_cons_of_pos, hy]
          rw [← cons_append]
          exact Perm.trans ih (Perm.cons x (Perm.swap y x ys))

    -- Combine permutations
    exact Perm.trans (Perm.append perm_l (Perm.cons x perm_r)) partition_perm.symm

/-- Quicksort produces a sorted output. -/
theorem qsort_sorted (xs : List α) : (qsort xs).Sorted (· ≤ ·) := by
  induction xs using qsort.induct with
  | case1 => simp [qsort]
  | case2 x xs ih_l ih_r =>
    simp only [qsort]
    -- Show qsort L ++ x :: qsort R is sorted
    apply sorted_append.mpr
    constructor
    · exact ih_l
    constructor
    · apply sorted_cons.mpr
      constructor
      · intro y hy
        -- y ∈ qsort L, so y ∈ L by permutation, so y ≤ x by filtering
        have h_perm : qsort (xs.filter (· ≤ x)) ~ xs.filter (· ≤ x) := qsort_perm _
        have : y ∈ xs.filter (· ≤ x) := Perm.mem_iff h_perm ▸ hy
        exact mem_filter_le this
      · exact ih_r
    · intro y hy z hz
      -- z ∈ qsort R, so z ∈ R by permutation, so x < z by filtering
      have h_perm : qsort (xs.filter (· > x)) ~ xs.filter (· > x) := qsort_perm _
      have : z ∈ xs.filter (· > x) := Perm.mem_iff h_perm ▸ hz
      exact le_of_lt (mem_filter_gt this)

end QuicksortVerification
