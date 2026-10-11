

import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.LinearAlgebra.BilinearForm.Basic

/-!
# Céa's Lemma - Bilinear Forms

Bilinearity, continuity bounds,
and coercivity bounds.
-/

namespace Cea

variable {V : Type*}
variable [NormedAddCommGroup V]
variable [NormedSpace ℝ V]

/-- Continuity bound for a bilinear form. -/
def HasContinuityBound
    (a : LinearMap.BilinForm ℝ V) (M : ℝ) : Prop :=
  ∀ u v : V, |a u v| ≤ M * ‖u‖ * ‖v‖

/-- Coercivity bound for a bilinear form. -/
def HasCoercivityBound
    (a : LinearMap.BilinForm ℝ V) (alpha : ℝ) : Prop :=
  ∀ v : V, alpha * ‖v‖ ^ 2 ≤ a v v

/-- Bilinearity in the first argument. -/
theorem bilinear_sub_left
    (a : LinearMap.BilinForm ℝ V)
    (u v w : V) :
    a (u - v) w = a u w - a v w := by
  exact LinearMap.map_sub₂ a u v w

/-- Bilinearity in the second argument. -/
theorem bilinear_sub_right
    (a : LinearMap.BilinForm ℝ V)
    (u v w : V) :
    a u (v - w) = a u v - a u w := by
  exact (a u).map_sub v w

/-- Apply continuity to approximation errors. -/
theorem continuity_error
    (a : LinearMap.BilinForm ℝ V)
    (M : ℝ)
    (hcont : HasContinuityBound a M)
    (u uh vh : V) :
    |a (u - uh) (u - vh)| ≤
      M * ‖u - uh‖ * ‖u - vh‖ := by
  exact hcont (u - uh) (u - vh)

/-- Apply coercivity to the Galerkin error. -/
theorem coercivity_error
    (a : LinearMap.BilinForm ℝ V)
    (alpha : ℝ)
    (hcoer : HasCoercivityBound a alpha)
    (u uh : V) :
    alpha * ‖u - uh‖ ^ 2 ≤
      a (u - uh) (u - uh) := by
  exact hcoer (u - uh)

/-- Coercivity with positive alpha implies
    nonnegativity on the diagonal. -/
theorem coercivity_nonneg
    (a : LinearMap.BilinForm ℝ V)
    (alpha : ℝ)
    (halpha : 0 < alpha)
    (hcoer : HasCoercivityBound a alpha)
    (v : V) :
    0 ≤ a v v := by
  have hnorm : 0 ≤ alpha * ‖v‖ ^ 2 := by
    exact mul_nonneg (le_of_lt halpha) (sq_nonneg ‖v‖)
  exact le_trans hnorm (hcoer v)

end Cea
