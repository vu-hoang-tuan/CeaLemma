
import CeaLemma.CeaBound


/-!
# Céa's Lemma - Final Theorem

The complete quasi-optimality estimate
using the infimum of approximation errors.
-/

namespace Cea

variable {V : Type*}
variable [NormedAddCommGroup V]
variable [NormedSpace ℝ V]

/-- The set of approximation errors. -/
def approxErrors
    (Vh : Submodule ℝ V) (u : V) : Set ℝ :=
  {r : ℝ | ∃ vh : V, vh ∈ Vh ∧ r = ‖u - vh‖}

/-- The approximation-error set is nonempty. -/
theorem approxErrors_nonempty
    (Vh : Submodule ℝ V) (u : V) :
    (approxErrors Vh u).Nonempty := by
  refine ⟨‖u - (0 : V)‖, ?_⟩
  exact ⟨0, Vh.zero_mem, rfl⟩

/-- Approximation errors are bounded below by zero. -/
theorem approxErrors_bddBelow
    (Vh : Submodule ℝ V) (u : V) :
    BddBelow (approxErrors Vh u) := by
  refine ⟨0, ?_⟩
  intro r hr
  obtain ⟨vh, _, hr⟩ := hr
  rw [hr]
  exact norm_nonneg (u - vh)

/-- Best approximation error as an infimum. -/
noncomputable def bestApproxError
    (Vh : Submodule ℝ V) (u : V) : ℝ :=
  sInf (approxErrors Vh u)

/-- The best approximation error is nonnegative. -/
theorem bestApproxError_nonneg
    (Vh : Submodule ℝ V) (u : V) :
    0 ≤ bestApproxError Vh u := by
  unfold bestApproxError
  apply le_csInf (approxErrors_nonempty Vh u)
  intro r hr
  obtain ⟨vh, _, hr⟩ := hr
  rw [hr]
  exact norm_nonneg (u - vh)

/-- The infimum is no larger than any
    admissible approximation error. -/
theorem bestApproxError_le
    (Vh : Submodule ℝ V) (u vh : V)
    (hvh : vh ∈ Vh) :
    bestApproxError Vh u ≤ ‖u - vh‖ := by
  unfold bestApproxError
  apply csInf_le (approxErrors_bddBelow Vh u)
  exact ⟨vh, hvh, rfl⟩

/-- Céa's Lemma: quasi-optimality of
    the Galerkin approximation. -/
theorem cea_lemma
    (a : LinearMap.BilinForm ℝ V)
    (Vh : Submodule ℝ V)
    (M alpha : ℝ)
    (hM : 0 ≤ M)
    (halpha : 0 < alpha)
    (hcont : HasContinuityBound a M)
    (hcoer : HasCoercivityBound a alpha)
    (u uh : V)
    (huh : uh ∈ Vh)
    (horth : IsGalerkinOrthogonal a Vh u uh) :
    ‖u - uh‖ ≤
      (M / alpha) * bestApproxError Vh u := by
  have hS : (approxErrors Vh u).Nonempty :=
    approxErrors_nonempty Vh u
  by_cases hM0 : M = 0
  · -- Case 1: M = 0.
    have h0 :
        ‖u - uh‖ ≤
          (M / alpha) * ‖u - (0 : V)‖ :=
      cea_pointwise a Vh M alpha hM halpha
        hcont hcoer u uh huh horth 0 Vh.zero_mem
    have hzero : ‖u - uh‖ ≤ 0 := by
      simpa [hM0] using h0
    simpa [hM0] using hzero
  · -- Case 2: M > 0.
    have hMpos : 0 < M :=
      lt_of_le_of_ne hM (Ne.symm hM0)
    have hcpos : 0 < M / alpha :=
      div_pos hMpos halpha
    -- The quotient is a lower bound
    -- for every approximation error.
    have hlow :
        ‖u - uh‖ / (M / alpha) ≤
          bestApproxError Vh u := by
      unfold bestApproxError
      apply le_csInf hS
      intro r hr
      obtain ⟨vh, hvh, hr⟩ := hr
      rw [hr]
      apply (div_le_iff₀ hcpos).2
      calc
        ‖u - uh‖ ≤
            (M / alpha) * ‖u - vh‖ :=
          cea_pointwise a Vh M alpha hM halpha
            hcont hcoer u uh huh horth vh hvh
        _ = ‖u - vh‖ * (M / alpha) :=
          mul_comm _ _
    -- Multiply back by the positive constant.
    have hfinal :=
      (div_le_iff₀ hcpos).1 hlow
    calc
      ‖u - uh‖ ≤
          bestApproxError Vh u * (M / alpha) := hfinal
      _ = (M / alpha) * bestApproxError Vh u :=
        mul_comm _ _

end Cea
