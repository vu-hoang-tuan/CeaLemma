import CeaLemma.CeaFinal

/-!
# Verification commands for Céa's lemma

This module displays the main declarations and the axioms on which `Cea.cea_lemma` depends.
The example below checks an application with all hypotheses supplied explicitly.

Run `lake env lean CeaLemma/Verify.lean` to display these diagnostics directly.
-/

#check Cea.cea_lemma
#check Cea.cea_pointwise
#check Cea.bestApproxError

#print axioms Cea.cea_lemma

section

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

example (a : LinearMap.BilinForm ℝ V) (Vh : Submodule ℝ V)
    (M alpha : ℝ) (hM : 0 ≤ M) (halpha : 0 < alpha)
    (hcont : Cea.HasContinuityBound a M) (hcoer : Cea.HasCoercivityBound a alpha)
    (u uh : V) (huh : uh ∈ Vh) (horth : Cea.IsGalerkinOrthogonal a Vh u uh) :
    ‖u - uh‖ ≤ (M / alpha) * Cea.bestApproxError Vh u :=
  Cea.cea_lemma a Vh M alpha hM halpha hcont hcoer u uh huh horth

end
