import CeaLemma.Galerkin
import Mathlib.Tactic.Ring

/-!
# The pointwise Céa estimate

This file bounds the Galerkin error by the error of any vector in the approximation subspace.

## Main results

* `Cea.cea_energy_bound`: combine coercivity, Galerkin orthogonality, and continuity.
* `Cea.cea_pointwise`: cancel the error norm to obtain the bound with constant `M / alpha`.

The cancellation treats the zero-error case separately, so no nonzero-error hypothesis is needed.
-/

namespace Cea

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Coercivity, Galerkin orthogonality, and continuity bound the squared error
by the product of the Galerkin error and any admissible approximation error. -/
theorem cea_energy_bound (a : LinearMap.BilinForm ℝ V) (Vh : Submodule ℝ V)
    (M alpha : ℝ) (hcont : HasContinuityBound a M) (hcoer : HasCoercivityBound a alpha)
    (u uh : V) (huh : uh ∈ Vh) (horth : IsGalerkinOrthogonal a Vh u uh)
    (vh : V) (hvh : vh ∈ Vh) :
    alpha * ‖u - uh‖ ^ 2 ≤ M * ‖u - uh‖ * ‖u - vh‖ := by
  calc
    alpha * ‖u - uh‖ ^ 2 ≤ a (u - uh) (u - uh) := hcoer (u - uh)
    _ = a (u - uh) (u - vh) := galerkin_error_identity a Vh u uh vh huh hvh horth
    _ ≤ |a (u - uh) (u - vh)| := le_abs_self _
    _ ≤ M * ‖u - uh‖ * ‖u - vh‖ := hcont (u - uh) (u - vh)

/-- The Galerkin error is at most `M / alpha` times the error of any `vh ∈ Vh`.
The continuity constant is nonnegative and the coercivity constant is strictly positive. -/
theorem cea_pointwise (a : LinearMap.BilinForm ℝ V) (Vh : Submodule ℝ V)
    (M alpha : ℝ) (hM : 0 ≤ M) (halpha : 0 < alpha)
    (hcont : HasContinuityBound a M) (hcoer : HasCoercivityBound a alpha)
    (u uh : V) (huh : uh ∈ Vh) (horth : IsGalerkinOrthogonal a Vh u uh)
    (vh : V) (hvh : vh ∈ Vh) :
    ‖u - uh‖ ≤ (M / alpha) * ‖u - vh‖ := by
  have hbound : alpha * ‖u - uh‖ ^ 2 ≤ M * ‖u - uh‖ * ‖u - vh‖ :=
    cea_energy_bound a Vh M alpha hcont hcoer u uh huh horth vh hvh
  by_cases he : ‖u - uh‖ = 0
  · have hrhs : 0 ≤ (M / alpha) * ‖u - vh‖ :=
      mul_nonneg (div_nonneg hM (le_of_lt halpha)) (norm_nonneg _)
    simpa only [he] using hrhs
  · -- Cancel the error norm only after proving that it is positive.
    have hepos : 0 < ‖u - uh‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm he)
    have hmul : ‖u - uh‖ * (alpha * ‖u - uh‖) ≤ ‖u - uh‖ * (M * ‖u - vh‖) := by
      calc
        ‖u - uh‖ * (alpha * ‖u - uh‖) = alpha * ‖u - uh‖ ^ 2 := by ring
        _ ≤ M * ‖u - uh‖ * ‖u - vh‖ := hbound
        _ = ‖u - uh‖ * (M * ‖u - vh‖) := by ring
    have hcancel : alpha * ‖u - uh‖ ≤ M * ‖u - vh‖ :=
      le_of_mul_le_mul_of_pos_left hmul hepos
    calc
      ‖u - uh‖ ≤ (M * ‖u - vh‖) / alpha := by
        apply (le_div_iff₀ halpha).2
        calc
          ‖u - uh‖ * alpha = alpha * ‖u - uh‖ := by ring
          _ ≤ M * ‖u - vh‖ := hcancel
      _ = (M / alpha) * ‖u - vh‖ := by ring

end Cea
