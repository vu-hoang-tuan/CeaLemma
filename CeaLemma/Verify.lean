
import CeaLemma.CeaFinal

/-!
# Verification of Céa's Lemma

Check the theorem, its dependencies,
and its mathematical statement.
-/

-- Check that the theorem exists.
#check Cea.cea_lemma

-- Check the pointwise estimate.
#check Cea.cea_pointwise

-- Check the best approximation error.
#check Cea.bestApproxError

-- Inspect the axioms used by the theorem.
#print axioms Cea.cea_lemma


section

variable {V : Type*}
variable [NormedAddCommGroup V]
variable [NormedSpace ℝ V]

example
    (a : LinearMap.BilinForm ℝ V)
    (Vh : Submodule ℝ V)
    (M alpha : ℝ)
    (hM : 0 ≤ M)
    (halpha : 0 < alpha)
    (hcont : Cea.HasContinuityBound a M)
    (hcoer : Cea.HasCoercivityBound a alpha)
    (u uh : V)
    (huh : uh ∈ Vh)
    (horth : Cea.IsGalerkinOrthogonal a Vh u uh) :
    ‖u - uh‖ ≤
      (M / alpha) * Cea.bestApproxError Vh u := by
  exact Cea.cea_lemma a Vh M alpha
    hM halpha hcont hcoer u uh huh horth

end
