import CeaLemma.BilinearForm
import CeaLemma.CeaBound
import CeaLemma.CeaFinal
import CeaLemma.Galerkin
import CeaLemma.Verify

/-!
# Céa's lemma

This library formalizes the quasi-optimality of Galerkin approximations for real bilinear forms
with continuity and coercivity bounds on normed vector spaces.

## Main results

* `Cea.galerkin_orthogonality`: derive orthogonality from the exact and discrete weak equations.
* `Cea.cea_pointwise`: bound the Galerkin error by any admissible approximation error.
* `Cea.cea_lemma`: bound the Galerkin error by `M / alpha` times the best approximation error.

All declarations are in the `Cea` namespace. This root module also imports `CeaLemma.Verify`,
which contains diagnostic commands and an explicit application of the main theorem.
-/
