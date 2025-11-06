import Mathlib.Tactic

/-!
# Topology: Composition of Continuous Functions

This file demonstrates a fundamental theorem in topology: the composition of
continuous functions is continuous. This is a cornerstone result used throughout
analysis and topology.

## Mathematical Background
In topology, a function f : X → Y between topological spaces is continuous if
the preimage of every open set in Y is open in X. This is equivalent to other
characterizations like preservation of limits.

## Main Result
If f : X → Y and g : Y → Z are continuous functions between topological spaces,
then their composition g ∘ f : X → Z is also continuous.
-/

-- Declare three topological spaces X, Y, Z
-- The square brackets indicate type class instances for the topology structure
variable (X Y Z : Type) [TopologicalSpace X]
[TopologicalSpace Y] [TopologicalSpace Z]

-- Declare continuous functions f : X → Y and g : Y → Z
variable (f : X → Y) (g: Y → Z)

/-!
## Theorem: Composition Preserves Continuity

**Statement**: If f and g are continuous, then g ∘ f is continuous.

**Proof Strategy**:
1. Use the definition of continuity via open sets
2. For any open set U in Z, show (g ∘ f)⁻¹'(U) is open in X
3. Key insight: (g ∘ f)⁻¹'(U) = f⁻¹'(g⁻¹'(U)) by composition properties
4. Apply continuity of g to get g⁻¹'(U) is open in Y
5. Apply continuity of f to get f⁻¹'(g⁻¹'(U)) is open in X
-/

example (hf : Continuous f) (hg : Continuous g) : Continuous (g ∘ f) := by
  -- Alternative one-liner proof using Mathlib's built-in theorem:
  -- exact Continuous.comp hg hf

  -- Manual proof to demonstrate the underlying mathematics:
  -- Expand the definition of continuity: f is continuous iff preimages of open sets are open
  rewrite [continuous_def] at *

  -- Let U be an arbitrary open set in Z
  intro U hU

  -- Goal: Show that (g ∘ f)⁻¹'(U) is open in X
  -- Strategy: Use the fact that (g ∘ f)⁻¹'(U) = f⁻¹'(g⁻¹'(U))

  -- Key lemma: preimage of composition equals composition of preimages
  -- This is true by definition (rfl = reflexivity of equality)
  have h_comp : (g ∘ f) ⁻¹' U = f ⁻¹' (g ⁻¹' U) := rfl
  rw [h_comp]

  -- Now we need to show f⁻¹'(g⁻¹'(U)) is open
  -- Step 1: Since g is continuous and U is open, g⁻¹'(U) is open in Y
  let V := g ⁻¹' U
  have hV : IsOpen V := hg U hU

  -- Step 2: Since f is continuous and V = g⁻¹'(U) is open, f⁻¹'(V) is open in X
  exact hf V hV
