
import CeaLemma.BilinearForm
import CeaLemma.Galerkin

/-!
# Céa's Lemma - Pointwise Error Estimate

We prove the Céa estimate for every
approximation vector vh in Vh.
-/

namespace Cea

variable {V : Type*}
variable [NormedAddCommGroup V]
variable [NormedSpace ℝ V]

/-- Step 1: Combine coercivity, Galerkin
orthogonality, and continuity. -/
theorem cea_energy_bound
    (a : LinearMap.BilinForm ℝ V)
    (Vh : Submodule ℝ V)
    (M alpha : ℝ)
    (hcont : HasContinuityBound a M)
    (hcoer : HasCoercivityBound a alpha)
    (u uh : V)
    (huh : uh ∈ Vh)
    (horth : IsGalerkinOrthogonal a Vh u uh)
    (vh : V)
    (hvh : vh ∈ Vh) :
    alpha * ‖u - uh‖ ^ 2 ≤
      M * ‖u - uh‖ * ‖u - vh‖ := by
  calc
    alpha * ‖u - uh‖ ^ 2
        ≤ a (u - uh) (u - uh) := hcoer (u - uh)
    _ = a (u - uh) (u - vh) :=
      galerkin_error_identity a Vh u uh vh huh hvh horth
    _ ≤ |a (u - uh) (u - vh)| := le_abs_self _
    _ ≤ M * ‖u - uh‖ * ‖u - vh‖ :=
      hcont (u - uh) (u - vh)

/-- Step 2: Céa's pointwise error estimate. -/
theorem cea_pointwise
    (a : LinearMap.BilinForm ℝ V)
    (Vh : Submodule ℝ V)
    (M alpha : ℝ)
    (hM : 0 ≤ M)
    (halpha : 0 < alpha)
    (hcont : HasContinuityBound a M)
    (hcoer : HasCoercivityBound a alpha)
    (u uh : V)
    (huh : uh ∈ Vh)
    (horth : IsGalerkinOrthogonal a Vh u uh)
    (vh : V)
    (hvh : vh ∈ Vh) :
    ‖u - uh‖ ≤ (M / alpha) * ‖u - vh‖ := by
  have hbound :
      alpha * ‖u - uh‖ ^ 2 ≤
        M * ‖u - uh‖ * ‖u - vh‖ :=
    cea_energy_bound a Vh M alpha
      hcont hcoer u uh huh horth vh hvh
  by_cases he : ‖u - uh‖ = 0
  · -- Case 1: The error is zero.
    have hrhs : 0 ≤ (M / alpha) * ‖u - vh‖ :=
      mul_nonneg
        (div_nonneg hM (le_of_lt halpha))
        (norm_nonneg _)
    simpa only [he] using hrhs
  · -- Case 2: The error is positive.
    have hepos : 0 < ‖u - uh‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm he)
    have hmul :
        ‖u - uh‖ * (alpha * ‖u - uh‖) ≤
          ‖u - uh‖ * (M * ‖u - vh‖) := by
      calc
        ‖u - uh‖ * (alpha * ‖u - uh‖) =
            alpha * ‖u - uh‖ ^ 2 := by ring
        _ ≤ M * ‖u - uh‖ * ‖u - vh‖ := hbound
        _ = ‖u - uh‖ * (M * ‖u - vh‖) := by ring
    have hcancel :
        alpha * ‖u - uh‖ ≤ M * ‖u - vh‖ := by
     exact le_of_mul_le_mul_of_pos_left hmul hepos
    calc
      ‖u - uh‖ ≤ (M * ‖u - vh‖) / alpha := by
        apply (le_div_iff₀ halpha).2
        calc
          ‖u - uh‖ * alpha =
              alpha * ‖u - uh‖ := by ring
          _ ≤ M * ‖u - vh‖ := hcancel
      _ = (M / alpha) * ‖u - vh‖ := by ring

end Cea
