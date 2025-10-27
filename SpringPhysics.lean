import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Spring Physics: Force as Negative Gradient of Potential Energy

This file contains a formal proof that for a spring system:
F(x) = -dU/dx

Where:
- F(x) = -kx is the spring force
- U(x) = (k/2)x² is the potential energy

This demonstrates the fundamental principle that conservative forces
are the negative gradient of potential energy.
-/

-- Define the spring constant as a parameter
variable (k : ℝ)

/-- The potential energy of a spring system -/
noncomputable def spring_energy (x : ℝ) : ℝ := (k / 2) * x^2

/-- The force exerted by a spring -/
def spring_force (x : ℝ) : ℝ := -k * x

/-- 
Main theorem: The spring force equals the negative derivative of potential energy.
This is a formal proof of F(x) = -dU/dx for the spring system.
-/
theorem spring_force_eq_negative_derivative (x : ℝ) :
  spring_force k x = -(deriv (spring_energy k) x) := by
  -- Unfold the definitions
  unfold spring_force spring_energy
  -- Compute the derivative of (k/2) * x^2
  simp only [deriv_const_mul, deriv_pow, one_mul]
  -- Simplify: deriv of x^2 is 2*x, so deriv of (k/2)*x^2 is k*x
  -- Therefore: -(k*x) = -k*x
  ring

/-- 
The spring force is conservative: there exists a potential function U 
such that F = -dU/dx
-/
theorem spring_force_is_conservative :
  ∃ U : ℝ → ℝ, ∀ x, spring_force k x = -(deriv U x) := by
  -- Use the spring energy as our potential function
  use spring_energy k
  -- Apply our main theorem
  intro x
  exact spring_force_eq_negative_derivative k x

/-- The spring energy function is differentiable everywhere -/
theorem spring_energy_differentiable : 
  Differentiable ℝ (spring_energy k) := by
  unfold spring_energy
  -- The function (k/2) * x^2 is differentiable as a polynomial
  apply Differentiable.const_mul
  exact differentiable_pow 2

/-- 
At equilibrium (x = 0), both force and energy derivative are zero
-/
theorem equilibrium_properties :
  spring_force k 0 = 0 ∧ deriv (spring_energy k) 0 = 0 := by
  constructor
  · -- Force at x = 0
    unfold spring_force
    simp
  · -- Energy derivative at x = 0  
    unfold spring_energy
    simp [deriv_const_mul, deriv_pow]

/--
The relationship F = -dU/dx holds for any spring constant k
-/
theorem universal_spring_relationship (k : ℝ) (x : ℝ) :
  spring_force k x = -(deriv (spring_energy k) x) :=
  spring_force_eq_negative_derivative k x

-- Example: verify the relationship for specific values
example : spring_force 2 3 = -(deriv (spring_energy 2) 3) := by
  exact spring_force_eq_negative_derivative 2 3

-- The proof can be extended to show energy conservation in dynamic systems
#check spring_force_eq_negative_derivative
#check spring_force_is_conservative
#check spring_energy_differentiable