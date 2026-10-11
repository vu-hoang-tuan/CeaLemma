

import CeaLemma.BilinearForm
import Mathlib.Tactic.Abel


/-!
# Céa's Lemma - Galerkin Orthogonality

Galerkin orthogonality and the error identity.
-/

namespace Cea

variable {V : Type*}
variable [NormedAddCommGroup V]
variable [NormedSpace ℝ V]

/-- Galerkin orthogonality condition. -/
def IsGalerkinOrthogonal
    (a : LinearMap.BilinForm ℝ V)
    (Vh : Submodule ℝ V)
    (u uh : V) : Prop :=
  ∀ v : V, v ∈ Vh → a (u - uh) v = 0

/-- Orthogonality follows from the two weak equations. -/
theorem galerkin_orthogonality
    (a : LinearMap.BilinForm ℝ V)
    (L : V →ₗ[ℝ] ℝ)
    (Vh : Submodule ℝ V)
    (u uh : V)
    (h_exact : ∀ v : V, a u v = L v)
    (h_discrete : ∀ v ∈ Vh, a uh v = L v) :
    IsGalerkinOrthogonal a Vh u uh := by
  intro v hv
  calc
    a (u - uh) v = a u v - a uh v := by
      exact LinearMap.map_sub₂ a u uh v
    _ = L v - L v := by
      rw [h_exact v, h_discrete v hv]
    _ = 0 := sub_self (L v)

/-- Fundamental error identity used in Céa's Lemma. -/
theorem galerkin_error_identity
    (a : LinearMap.BilinForm ℝ V)
    (Vh : Submodule ℝ V)
    (u uh vh : V)
    (huh : uh ∈ Vh)
    (hvh : vh ∈ Vh)
    (horth : IsGalerkinOrthogonal a Vh u uh) :
    a (u - uh) (u - uh) =
      a (u - uh) (u - vh) := by
  have hmem : vh - uh ∈ Vh := by
    exact Vh.sub_mem hvh huh
  have hzero : a (u - uh) (vh - uh) = 0 := by
    exact horth (vh - uh) hmem
  have hsplit :
      u - uh = (u - vh) + (vh - uh) := by
    abel
  calc
    a (u - uh) (u - uh) =
        a (u - uh) ((u - vh) + (vh - uh)) := by
      exact congrArg (fun w : V => a (u - uh) w) hsplit
    _ = a (u - uh) (u - vh) +
          a (u - uh) (vh - uh) := by
      exact (a (u - uh)).map_add (u - vh) (vh - uh)
    _ = a (u - uh) (u - vh) := by
      rw [hzero, add_zero]

end Cea
