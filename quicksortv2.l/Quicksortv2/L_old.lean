import Quicksortv2.L.Basic

--
--  Quicksort correctness in Lean 4 + mathlib

--  Requires:
--    - Lean 4
--    - mathlib (e.g., via `lake exe cache get` in a mathlib starter project)
--

import Mathlib.Data.List.Permutation
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Sort
import Mathlib.Order.Basic

open List

namespace QS

variable {α : Type*} [LinearOrder α] [DecidableRel (· ≤ · : α → α → Prop)]

/-- Standard functional quicksort, pivot = head, two-way partition by (≤ pivot) / (> pivot). -/
def qsort : List α → List α
| []       => []
| (x :: xs) =>
  let L := xs.filter (· ≤ x)
  let R := xs.filter (· > x)
  qsort L ++ x :: qsort R
termination_by l => l.length
decreasing_by
  -- Length decreases since both filters are sublists of `xs`
  all_goals
    simp_wf
    rw [List.length_attach]
    exact Nat.lt_of_le_of_lt (List.length_filter_le _ _) (Nat.lt_succ_self _)/-!
Helper facts about membership and (co)bounds of the filtered partitions.
-/

/-- All elements of `xs.filter (· ≤ x)` are `≤ x`. -/
lemma mem_filter_le_pivot {x y : α} {xs : List α}
  (hy : y ∈ xs.filter (· ≤ x)) : y ≤ x := by
  rw [List.mem_filter] at hy
  exact decide_eq_true_iff.mp hy.2

/-- All elements of `xs.filter (· > x)` are `> x`. -/
lemma mem_filter_gt_pivot {x y : α} {xs : List α}
  (hy : y ∈ xs.filter (· > x)) : x < y := by
  rw [List.mem_filter] at hy
  exact decide_eq_true_iff.mp hy.2

/-- Every element of `xs` goes to exactly one side of the pivot split. -/
lemma mem_of_filter_split {x y : α} {xs : List α} :
    y ∈ xs ↔ y ∈ xs.filter (· ≤ x) ∨ y ∈ xs.filter (· > x) := by
  constructor
  · intro hy
    by_cases h : y ≤ x
    · left
      rw [List.mem_filter]
      exact ⟨hy, decide_eq_true_iff.mpr h⟩
    · right
      have : x < y := lt_of_not_ge h
      rw [List.mem_filter]
      exact ⟨hy, decide_eq_true_iff.mpr this⟩
  · intro h
    cases h with
    | inl h =>
      rw [List.mem_filter] at h
      exact h.1
    | inr h =>
      rw [List.mem_filter] at h
      exact h.1

/-- The "split" is a permutation of putting pivot in front: `L ++ x :: R ~ x :: xs`. -/
lemma perm_partition (x : α) (xs : List α) :
    xs.filter (· ≤ x) ++ x :: xs.filter (· > x) ~ x :: xs := by
  -- Induction on `xs`
  induction xs with
  | nil => simp
  | cons y ys ih =>
    by_cases h : y ≤ x
    · -- `y` goes to the left
      simp only [List.filter_cons_of_pos _ (decide_eq_true_iff.mpr h)]
      simp only [List.filter_cons_of_neg _ (fun h_gt =>
        not_lt.mpr h (decide_eq_true_iff.mp h_gt))]
      simp only [List.cons_append]
      exact List.Perm.cons y ih
    · -- `y` goes to the right: `¬ y ≤ x` ⇒ `x < y` by linearity
      have hy : x < y := lt_of_not_ge h
      simp only [List.filter_cons_of_neg _ (decide_eq_true_iff.mp ∘ mt decide_eq_true_iff.mpr $ h)]
      simp only [List.filter_cons_of_pos _ (decide_eq_true_iff.mpr hy)]
      simp only [List.nil_append, List.cons_append]
      rw [← List.cons_append]
      exact List.Perm.trans ih (List.Perm.cons x (List.Perm.swap y x ys))

/-!
Sortedness: we show an invariant that everything on the left is `≤ x`
and everything on the right is `≥ x` (actually `>` in our split), and
combine `Sorted` lists with a pivot sandwiched by bounds.
-/

/-- Every element of `xs.filter (· ≤ x)` is ≤ `x`. -/
lemma all_le_left (x : α) (xs : List α) :
    ∀ {y}, y ∈ xs.filter (· ≤ x) → y ≤ x := @mem_filter_le_pivot _ _ x

/-- Every element of `xs.filter (· > x)` is ≥ `x`. -/
lemma all_ge_right (x : α) (xs : List α) :
    ∀ {y}, y ∈ xs.filter (· > x) → x ≤ y :=
  fun hy => le_of_lt (mem_filter_gt_pivot hy)

/-- If `l` is sorted, `r` is sorted, every element of `l` ≤ `x` and `x` ≤ every element of `r`,
then `l ++ x :: r` is sorted. -/
lemma sorted_append_pivot
  {l r : List α} {x : α}
  (hl : l.Sorted (· ≤ ·)) (hr : r.Sorted (· ≤ ·))
  (hle : ∀ {y}, y ∈ l → y ≤ x) (hge : ∀ {y}, y ∈ r → x ≤ y)
  : (l ++ x :: r).Sorted (· ≤ ·) := by
  apply List.Sorted.append hl
  apply List.Sorted.cons
  · intro y hy
    exact hle hy
  · apply List.Sorted.append (List.sorted_singleton _) hr
    intros y _ z hz
    exact hge hz

/-!
Main theorems: qsort is a permutation and preserves sortedness.
-/

/-- Quicksort produces a permutation of the input. -/
theorem qsort_perm (xs : List α) : qsort xs ~ xs := by
  induction xs using qsort.induct with
  | case1 => simp [qsort]
  | case2 x xs ih_l ih_r =>
    simp only [qsort]
    rw [← List.singleton_append]
    exact List.Perm.trans (List.Perm.append ih_l (List.Perm.cons x ih_r))
      (perm_partition x xs).symm

/-- Quicksort produces a sorted list. -/
theorem qsort_sorted (xs : List α) : (qsort xs).Sorted (· ≤ ·) := by
  induction xs using qsort.induct with
  | case1 => simp [qsort, List.sorted_nil]
  | case2 x xs ih_l ih_r =>
    simp only [qsort]
    apply sorted_append_pivot ih_l ih_r
    · intro y hy
      have : y ∈ xs.filter (· ≤ x) := by
        rwa [← List.perm_comm.mp (qsort_perm (xs.filter (· ≤ x)))]
      exact all_le_left x xs this
    · intro y hy
      have : y ∈ xs.filter (· > x) := by
        rwa [← List.perm_comm.mp (qsort_perm (xs.filter (· > x)))]
      exact all_ge_right x xs this

end QS
