import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.LinearAlgebra.BilinearForm.Basic

/-!
# Bounds for real bilinear forms

This file introduces the bounds used in Céa's lemma on a real normed vector space.

## Main definitions

* `Cea.HasContinuityBound`: an absolute-value bound with constant `M`.
* `Cea.HasCoercivityBound`: a lower bound on the diagonal with constant `alpha`.

The definitions record only the inequalities. Sign assumptions on the constants are supplied
separately when needed. No completeness or symmetry assumption is imposed.
-/

namespace Cea

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The bilinear form `a` satisfies `|a u v| ≤ M * ‖u‖ * ‖v‖` for all `u` and `v`.
Nonnegativity of `M` is a separate hypothesis in the error estimates. -/
def HasContinuityBound (a : LinearMap.BilinForm ℝ V) (M : ℝ) : Prop :=
  ∀ u v : V, |a u v| ≤ M * ‖u‖ * ‖v‖

/-- The bilinear form `a` satisfies `alpha * ‖v‖ ^ 2 ≤ a v v` for all `v`.
Positivity of `alpha` is a separate hypothesis in the error estimates. -/
def HasCoercivityBound (a : LinearMap.BilinForm ℝ V) (alpha : ℝ) : Prop :=
  ∀ v : V, alpha * ‖v‖ ^ 2 ≤ a v v

/-- A bilinear form preserves subtraction in its first argument. -/
theorem bilinear_sub_left (a : LinearMap.BilinForm ℝ V) (u v w : V) :
    a (u - v) w = a u w - a v w :=
  LinearMap.map_sub₂ a u v w

/-- A bilinear form preserves subtraction in its second argument. -/
theorem bilinear_sub_right (a : LinearMap.BilinForm ℝ V) (u v w : V) :
    a u (v - w) = a u v - a u w :=
  (a u).map_sub v w

/-- Apply the continuity bound to the Galerkin error and an approximation error. -/
theorem continuity_error (a : LinearMap.BilinForm ℝ V) (M : ℝ)
    (hcont : HasContinuityBound a M) (u uh vh : V) :
    |a (u - uh) (u - vh)| ≤ M * ‖u - uh‖ * ‖u - vh‖ :=
  hcont (u - uh) (u - vh)

/-- Apply the coercivity bound to the Galerkin error. -/
theorem coercivity_error (a : LinearMap.BilinForm ℝ V) (alpha : ℝ)
    (hcoer : HasCoercivityBound a alpha) (u uh : V) :
    alpha * ‖u - uh‖ ^ 2 ≤ a (u - uh) (u - uh) :=
  hcoer (u - uh)

/-- A coercivity bound with positive constant makes the bilinear form nonnegative
on the diagonal. -/
theorem coercivity_nonneg (a : LinearMap.BilinForm ℝ V) (alpha : ℝ)
    (halpha : 0 < alpha) (hcoer : HasCoercivityBound a alpha) (v : V) :
    0 ≤ a v v := by
  have hnorm : 0 ≤ alpha * ‖v‖ ^ 2 :=
    mul_nonneg (le_of_lt halpha) (sq_nonneg ‖v‖)
  exact le_trans hnorm (hcoer v)

end Cea
