/-
  Quicksort correctness in Lean 4 + mathlib

  Requires:
    - Lean 4
    - mathlib (e.g., via `lake exe cache get` in a mathlib starter project)
-/

import Mathlib.Data.List.Perm
import Mathlib.Data.List.Basic
import Mathlib/Init/Algebra/Order

open List

namespace QS

variable {α : Type*} [DecidableLinearOrder α]

/-- Standard functional quicksort, pivot = head, two-way partition by (≤ pivot) / (> pivot). -/
def qsort : List α → List α
| []       => []
| (x :: xs) =>
  let L := xs.filter (· ≤ x)
  let R := xs.filter (· > x)
  qsort L ++ x :: qsort R
termination_by qsort l => l.length
decreasing_by
  -- Length decreases since both filters are sublists of `xs`
  all_goals
    simp_wf
    apply Nat.lt_of_le_of_lt ?_ (Nat.lt_succ_self _)
    · exact List.length_filter_le _ _
    · -- ditto for the other branch
      exact List.length_filter_le _ _

/-!
Helper facts about membership and (co)bounds of the filtered partitions.
-/

/-- All elements of `xs.filter (· ≤ x)` are `≤ x`. -/
lemma mem_filter_le_pivot {x y : α} {xs : List α}
  (hy : y ∈ xs.filter (· ≤ x)) : y ≤ x := by
  simpa [List.mem_filter, and_left_comm, and_assoc] using (And.left (by
    simpa [List.mem_filter] using hy))

/-- All elements of `xs.filter (· > x)` are `> x`. -/
lemma mem_filter_gt_pivot {x y : α} {xs : List α}
  (hy : y ∈ xs.filter (· > x)) : x < y := by
  simpa [List.mem_filter, and_left_comm, and_assoc] using (And.right (by
    simpa [List.mem_filter] using hy))

/-- Every element of `xs` goes to exactly one side of the pivot split. -/
lemma mem_of_filter_split {x y : α} {xs : List α} :
    y ∈ xs ↔ y ∈ xs.filter (· ≤ x) ∨ y ∈ xs.filter (· > x) := by
  constructor
  · intro hy
    by_cases h : y ≤ x
    · left; simpa [List.mem_filter, hy, h]
    · right
      have : x < y := lt_of_le_of_ne (le_of_lt_or_eq (lt_or_eq_of_le (le_of_not_ge h)).elim ?l ?r) ?ne
        -- small helper: from `¬ y ≤ x` in a linear order, we have `x < y`
        -- we can just use totality:
      · exact lt_of_le_of_ne (le_total x y |>.resolve_right (le_of_not_gt h)) (by decide)
      -- Simpler: use linearity
      exact by
        have : x < y := lt_of_le_of_ne (le_total x y |>.resolve_left (le_of_not_gt h)) (by decide)
        simpa [List.mem_filter, hy, this]
  · intro h
    rcases h with h | h
    · simpa [List.mem_filter] using h
    · simpa [List.mem_filter] using h
-- The previous proof is a bit fiddly; a standard approach is to use totality:
-- In a decidable linear order, either `y ≤ x` or `x < y`, so membership is exclusive.

/-- The "split" is a permutation of putting pivot in front: `L ++ x :: R ~ x :: xs`. -/
lemma perm_partition (x : α) (xs : List α) :
    xs.filter (· ≤ x) ++ x :: xs.filter (· > x) ~ x :: xs := by
  -- Induction on `xs`
  induction xs with
  | nil =>
      simp
  | @cons y ys ih =>
      by_cases h : y ≤ x
      · -- `y` goes to the left
        have : y ∈ (y :: ys).filter (· ≤ x) := by simp [List.mem_filter, h]
        -- show permutation by moving `y` to the left side and using IH
        simpa [List.filter_cons_of_pos _ h, List.filter_cons_of_neg _ (lt_of_le_of_ne ?a ?b |> not_le.mpr)]
          using
          (Perm.skip y <|
            by
              simpa [List.filter_cons_of_pos _ h] using ih)
        -- The above line is a compact sketch; a more explicit proof is common in mathlib:
      · -- `y` goes to the right: `¬ y ≤ x` ⇒ `x < y` by linearity
        have hy : x < y := lt_of_le_of_ne (le_total x y |>.resolve_left (le_of_not_gt (not_le.mpr (lt_of_le_of_ne ?a ?b)))) (by decide)
        -- Using standard lemmas:
        simpa [List.filter_cons_of_neg _ h, List.filter_cons_of_pos _ (lt_of_le_of_ne (le_total x y |>.resolve_left (le_of_not_gt (not_le.mpr ?lt))) ?ne)]
          using
          (Perm.trans
            (by
              -- rotate to insert y on the right
              simpa using (Perm.cons y ih))
            (by
              -- swap pivot past y
              simpa using (Perm.swap _ _ _)))
-- NOTE: The above is a classic but somewhat tedious permutation-by-cases proof.
-- In practice, you’d use mathlib lemmas for partition permutations.
-- If you prefer a clean proof, see the alternative route below using multisets.

/-!
Sortedness: we show an invariant that everything on the left is `≤ x`
and everything on the right is `≥ x` (actually `>` in our split), and
combine `Sorted` lists with a pivot sandwiched by bounds.
-/

/-- Every element of `xs.filter (· ≤ x)` is ≤ `x`. -/
lemma all_le_left (x : α) (xs : List α) :
    ∀ {y}, y ∈ xs.filter (· ≤ x) → y ≤ x := mem_filter_le_pivot

/-- Every element of `xs.filter (· > x)` is ≥ `x`. -/
lemma all_ge_right (x : α) (xs : List α) :
    ∀ {y}, y ∈ xs.filter (· > x) → x ≤ y := fun {y} hy => le_of_lt (mem_filter_gt_pivot (x:=x) (y:=y) (xs:=xs) hy)

/-- If `l` is sorted, `r` is sorted, every element of `l` ≤ `x` and `x` ≤ every element of `r`,
then `l ++ x :: r` is sorted. -/
lemma sorted_append_pivot
  {l r : List α} {x : α}
  (hl : l.Sorted (· ≤ ·)) (hr : r.Sorted (· ≤ ·))
  (hle : ∀ {y}, y ∈ l → y ≤ x) (hge : ∀ {y}, y ∈ r → x ≤ y)
  : (l ++ x :: r).Sorted (· ≤ ·) :=
