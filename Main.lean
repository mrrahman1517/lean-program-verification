import RigorousSpringPhysics

/-!
# Main Demo File for Spring Physics Verification

This file serves as a demonstration of how to use the proven theorems from
RigorousSpringPhysics.lean. It shows how formal verification can be combined
with practical examples in a Lean 4 project.

## Purpose

This file demonstrates:
1. How to import and use formally verified theorems
2. How to create examples that use proven mathematical relationships
3. How to structure a Lean project with multiple modules

## Usage

The main executable is defined in RigorousSpringPhysics.lean.
Run with: `lake exe rigorous`

## Integration

This file imports from RigorousSpringPhysics and demonstrates the use of:
- ForceDefinition and EnergyDefinition propositions
- Proven theorems about spring physics
- Computational verification functions

Part of the lean-program-verification project.
-/

/--
Demo file that shows the theorems from RigorousSpringPhysics.
This file demonstrates how to use the proven theorems.
-/

-- We can check our theorems are available
example : ForceDefinition 1.0 2.0 := force_def_correct 1.0 2.0
example : EnergyDefinition 1.0 2.0 := energy_def_correct 1.0 2.0

-- Demo function (renamed to avoid conflict with main in RigorousSpringPhysics)
def demo : IO Unit := do
  IO.println "Spring Physics Demo - Using Proven Theorems"
  IO.println "===========================================" 
  IO.println ""
  IO.println "This file demonstrates the use of formally proven theorems"
  IO.println "from RigorousSpringPhysics.lean"
  IO.println ""
  IO.println "Available proven theorems:"
  IO.println "• ForceDefinition: F(x) = -kx is correct"
  IO.println "• EnergyDefinition: U(x) = (k/2)x² is correct"
  IO.println "• equilibrium_theorem: F(0) = 0 ∧ U(0) = 0"
  IO.println "• force_linearity: F(x₁+x₂) = F(x₁) + F(x₂)"
  IO.println "• energy_scaling: U_k₁+k₂(x) = U_k₁(x) + U_k₂(x)"
  IO.println ""
  IO.println "Numerical examples:"
  IO.println s!"F(1, 2) = {spring_force 1.0 2.0}"
  IO.println s!"U(1, 2) = {spring_energy 1.0 2.0}"
  IO.println s!"F = -dU/dx verified: {verify_relationship 1.0 1.0}"
  IO.println ""
  IO.println "All theorems are formally verified in Lean 4!"

-- The main function is already defined in RigorousSpringPhysics
-- Run with: lake exe rigorous
