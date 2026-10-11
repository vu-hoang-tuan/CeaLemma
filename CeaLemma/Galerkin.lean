import CeaLemma.BilinearForm
import Mathlib.Tactic.Abel

/-!
# Galerkin orthogonality

This file derives Galerkin orthogonality from the exact and discrete weak equations and proves
the error identity used in Céa's lemma.

## Main declarations

* `Cea.IsGalerkinOrthogonal`: the error is orthogonal to the subspace with respect to `a`.
* `Cea.galerkin_orthogonality`: the two weak equations imply Galerkin orthogonality.
* `Cea.galerkin_error_identity`: replace the second error argument by `u - vh`.

Orthogonality is expressed using the bilinear form, not an inner product.
-/

namespace Cea

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The error `u - uh` is orthogonal to every vector in `Vh` with respect to `a`.
Membership of `uh` in `Vh` is a separate hypothesis in the error estimates. -/
def IsGalerkinOrthogonal (a : LinearMap.BilinForm ℝ V) (Vh : Submodule ℝ V)
    (u uh : V) : Prop :=
  ∀ v : V, v ∈ Vh → a (u - uh) v = 0

/-- Solutions of the exact and discrete weak equations satisfy Galerkin orthogonality. -/
theorem galerkin_orthogonality (a : LinearMap.BilinForm ℝ V) (L : V →ₗ[ℝ] ℝ)
    (Vh : Submodule ℝ V) (u uh : V)
    (h_exact : ∀ v : V, a u v = L v) (h_discrete : ∀ v ∈ Vh, a uh v = L v) :
    IsGalerkinOrthogonal a Vh u uh := by
  intro v hv
  calc
    a (u - uh) v = a u v - a uh v := bilinear_sub_left a u uh v
    _ = L v - L v := by rw [h_exact v, h_discrete v hv]
    _ = 0 := sub_self (L v)

/-- Galerkin orthogonality identifies `a (u - uh) (u - uh)` with `a (u - uh) (u - vh)`
for any `uh` and `vh` in the approximation subspace. -/
theorem galerkin_error_identity (a : LinearMap.BilinForm ℝ V) (Vh : Submodule ℝ V)
    (u uh vh : V) (huh : uh ∈ Vh) (hvh : vh ∈ Vh)
    (horth : IsGalerkinOrthogonal a Vh u uh) :
    a (u - uh) (u - uh) = a (u - uh) (u - vh) := by
  have hmem : vh - uh ∈ Vh := Vh.sub_mem hvh huh
  have hzero : a (u - uh) (vh - uh) = 0 := horth (vh - uh) hmem
  have hsplit : u - uh = (u - vh) + (vh - uh) := by abel
  calc
    a (u - uh) (u - uh) = a (u - uh) ((u - vh) + (vh - uh)) :=
      congrArg (fun w : V ↦ a (u - uh) w) hsplit
    _ = a (u - uh) (u - vh) + a (u - uh) (vh - uh) :=
      (a (u - uh)).map_add (u - vh) (vh - uh)
    _ = a (u - uh) (u - vh) := by rw [hzero, add_zero]

end Cea
