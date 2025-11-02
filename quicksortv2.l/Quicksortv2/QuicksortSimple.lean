import Quicksortv2.L.Basic
import Mathlib.Data.List.Permutation
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Sort

open List

namespace QuicksortVerification

variable {α : Type*} [LinearOrder α] [DecidableRel (· ≤ · : α → α → Prop)]

/-- Simple functional quicksort implementation -/
def qsort : List α → List α
| [] => []
| (x :: xs) =>
  let left := xs.filter (· ≤ x)
  let right := xs.filter (· > x)
  qsort left ++ [x] ++ qsort right
termination_by l => l.length
decreasing_by
  all_goals
    simp_wf
    exact Nat.lt_succ_of_le (List.length_filter_le _ _)

/-- Helper lemma: elements in left partition are ≤ pivot -/
lemma filter_le_mem {x y : α} {xs : List α} (h : y ∈ xs.filter (· ≤ x)) : y ≤ x := by
  rw [mem_filter] at h
  exact decide_eq_true_iff.mp h.2

/-- Helper lemma: elements in right partition are > pivot -/
lemma filter_gt_mem {x y : α} {xs : List α} (h : y ∈ xs.filter (· > x)) : x < y := by
  rw [mem_filter] at h
  exact decide_eq_true_iff.mp h.2

/-- Quicksort preserves all elements (permutation property) -/
theorem qsort_perm (xs : List α) : qsort xs ~ xs := by
  induction xs with
  | nil => simp [qsort]
  | cons x xs ih =>
    simp [qsort]
    sorry -- Proof requires more complex permutation reasoning

/-- Quicksort produces sorted output -/
theorem qsort_sorted (xs : List α) : (qsort xs).Sorted (· ≤ ·) := by
  induction xs with
  | nil => simp [qsort]
  | cons x xs ih =>
    simp [qsort]
    sorry -- Proof requires sorted append reasoning

#check qsort
#check qsort_perm
#check qsort_sorted

end QuicksortVerification
