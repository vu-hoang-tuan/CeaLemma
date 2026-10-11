import CeaLemma.CeaBound

/-!
# Céa's lemma

This file passes from the pointwise Céa estimate to an estimate in terms of the infimum of all
admissible approximation errors.

## Main declarations

* `Cea.approxErrors`: the set of errors `‖u - vh‖` for `vh ∈ Vh`.
* `Cea.bestApproxError`: the infimum of this nonempty, bounded-below set.
* `Cea.cea_lemma`: quasi-optimality of the Galerkin approximation with constant `M / alpha`.

The argument does not require the infimum to be attained. In particular, no closedness or
finite-dimensionality assumption on `Vh` is needed.
-/

namespace Cea

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The set of norm errors obtained by approximating `u` with vectors in `Vh`. -/
def approxErrors (Vh : Submodule ℝ V) (u : V) : Set ℝ :=
  {r : ℝ | ∃ vh : V, vh ∈ Vh ∧ r = ‖u - vh‖}

/-- The approximation-error set is nonempty because `0 ∈ Vh`. -/
theorem approxErrors_nonempty (Vh : Submodule ℝ V) (u : V) :
    (approxErrors Vh u).Nonempty := by
  refine ⟨‖u - (0 : V)‖, ?_⟩
  exact ⟨0, Vh.zero_mem, rfl⟩

/-- Approximation errors are bounded below by zero. -/
theorem approxErrors_bddBelow (Vh : Submodule ℝ V) (u : V) :
    BddBelow (approxErrors Vh u) := by
  refine ⟨0, ?_⟩
  intro r hr
  obtain ⟨vh, _, hr⟩ := hr
  rw [hr]
  exact norm_nonneg (u - vh)

/-- The infimum of the norm errors of approximating `u` in `Vh`.
This definition does not assert the existence of a minimizing vector. -/
noncomputable def bestApproxError (Vh : Submodule ℝ V) (u : V) : ℝ :=
  sInf (approxErrors Vh u)

/-- The best approximation error is nonnegative. -/
theorem bestApproxError_nonneg (Vh : Submodule ℝ V) (u : V) :
    0 ≤ bestApproxError Vh u := by
  unfold bestApproxError
  apply le_csInf (approxErrors_nonempty Vh u)
  intro r hr
  obtain ⟨vh, _, hr⟩ := hr
  rw [hr]
  exact norm_nonneg (u - vh)

/-- The best approximation error is no larger than the error of any `vh ∈ Vh`. -/
theorem bestApproxError_le (Vh : Submodule ℝ V) (u vh : V) (hvh : vh ∈ Vh) :
    bestApproxError Vh u ≤ ‖u - vh‖ := by
  unfold bestApproxError
  apply csInf_le (approxErrors_bddBelow Vh u)
  exact ⟨vh, hvh, rfl⟩

/-- **Céa's lemma**: a Galerkin approximation `uh ∈ Vh` has error at most `M / alpha`
times the best approximation error in `Vh`.

The hypotheses give a continuity bound with `0 ≤ M`, a coercivity bound with `0 < alpha`,
and Galerkin orthogonality. Existence of the exact and discrete solutions is not asserted. -/
theorem cea_lemma (a : LinearMap.BilinForm ℝ V) (Vh : Submodule ℝ V)
    (M alpha : ℝ) (hM : 0 ≤ M) (halpha : 0 < alpha)
    (hcont : HasContinuityBound a M) (hcoer : HasCoercivityBound a alpha)
    (u uh : V) (huh : uh ∈ Vh) (horth : IsGalerkinOrthogonal a Vh u uh) :
    ‖u - uh‖ ≤ (M / alpha) * bestApproxError Vh u := by
  by_cases hM0 : M = 0
  · -- The zero continuity constant is handled without division by `M / alpha`.
    have h0 : ‖u - uh‖ ≤ (M / alpha) * ‖u - (0 : V)‖ :=
      cea_pointwise a Vh M alpha hM halpha hcont hcoer u uh huh horth 0 Vh.zero_mem
    simpa [hM0] using h0
  · have hMpos : 0 < M := lt_of_le_of_ne hM (Ne.symm hM0)
    have hcpos : 0 < M / alpha := div_pos hMpos halpha
    -- The scaled Galerkin error is a lower bound for every approximation error.
    have hlow : ‖u - uh‖ / (M / alpha) ≤ bestApproxError Vh u := by
      unfold bestApproxError
      apply le_csInf (approxErrors_nonempty Vh u)
      intro r hr
      obtain ⟨vh, hvh, hr⟩ := hr
      rw [hr]
      apply (div_le_iff₀ hcpos).2
      calc
        ‖u - uh‖ ≤ (M / alpha) * ‖u - vh‖ :=
          cea_pointwise a Vh M alpha hM halpha hcont hcoer u uh huh horth vh hvh
        _ = ‖u - vh‖ * (M / alpha) := mul_comm _ _
    calc
      ‖u - uh‖ ≤ bestApproxError Vh u * (M / alpha) := (div_le_iff₀ hcpos).1 hlow
      _ = (M / alpha) * bestApproxError Vh u := mul_comm _ _

end Cea
