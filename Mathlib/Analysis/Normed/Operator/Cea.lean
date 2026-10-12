/-
Copyright (c) 2026 Vũ Hoàng Tuấn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vũ Hoàng Tuấn
-/
module

public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Céa's lemma

Let `B` be a continuous bilinear form on a real seminormed space, with coercivity constant
`α > 0`. If `uₕ ∈ K` and `B (u - uₕ) v = 0` for every `v ∈ K`, then the Galerkin error
`‖u - uₕ‖` is at most `‖B‖ / α` times the distance from `u` to `K`.

## Main results

* `ContinuousLinearMap.norm_sub_le_mul_norm_sub_of_bound`: the error estimate for each
  comparison vector, using any upper bound `M` on the operator norm.
* `ContinuousLinearMap.norm_sub_le_mul_infDist_of_bound`: **Céa's lemma** with constant `M / α`.
* `ContinuousLinearMap.norm_sub_le_mul_infDist`: Céa's lemma with constant `‖B‖ / α`.
* `IsCoercive.exists_norm_sub_le_mul_infDist`: a coercive form admits one quasi-optimality
  constant for all subspaces and all Galerkin approximations.

The coercivity bound uses the same normalization as `IsCoercive`. Galerkin orthogonality is
stated directly; it follows from the exact and discrete variational equations by
`ContinuousLinearMap.map_sub₂`. Neither completeness, symmetry, closedness of the subspace,
nor finite dimensionality is required. The infimum need not be attained.

## Tags

Céa, Galerkin, coercive, quasi-optimality, approximation
-/

public section

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

namespace ContinuousLinearMap

variable (B : E →L[ℝ] E →L[ℝ] ℝ) {K : Submodule ℝ E} {u uₕ vₕ : E} {M α : ℝ}

/-- The Galerkin error is bounded by `M / α` times the error of any comparison vector in `K`,
where `M` bounds the operator norm and `α` is a positive coercivity constant. -/
theorem norm_sub_le_mul_norm_sub_of_bound (hcont : ‖B‖ ≤ M) (hα : 0 < α)
    (hcoer : ∀ v, α * ‖v‖ * ‖v‖ ≤ B v v) (huₕ : uₕ ∈ K)
    (horth : ∀ v ∈ K, B (u - uₕ) v = 0) (hvₕ : vₕ ∈ K) :
    ‖u - uₕ‖ ≤ (M / α) * ‖u - vₕ‖ := by
  by_cases h : ‖u - uₕ‖ = 0
  · rw [h]
    exact mul_nonneg (div_nonneg ((norm_nonneg B).trans hcont) hα.le) (norm_nonneg _)
  have hpos : 0 < ‖u - uₕ‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h)
  have hidentity : B (u - uₕ) (u - uₕ) = B (u - uₕ) (u - vₕ) := by
    calc
      B (u - uₕ) (u - uₕ) = B (u - uₕ) ((u - vₕ) + (vₕ - uₕ)) :=
        congrArg (B (u - uₕ)) (sub_add_sub_cancel u vₕ uₕ).symm
      _ = B (u - uₕ) (u - vₕ) := by
        rw [map_add, horth (vₕ - uₕ) (K.sub_mem hvₕ huₕ), add_zero]
  have hbound : α * ‖u - uₕ‖ * ‖u - uₕ‖ ≤ M * ‖u - vₕ‖ * ‖u - uₕ‖ := calc
    α * ‖u - uₕ‖ * ‖u - uₕ‖ ≤ B (u - uₕ) (u - uₕ) := hcoer _
    _ = B (u - uₕ) (u - vₕ) := hidentity
    _ ≤ ‖B (u - uₕ) (u - vₕ)‖ := by simpa only [Real.norm_eq_abs] using le_abs_self _
    _ ≤ M * ‖u - uₕ‖ * ‖u - vₕ‖ := B.le_of_opNorm₂_le_of_le hcont le_rfl le_rfl
    _ = M * ‖u - vₕ‖ * ‖u - uₕ‖ := mul_right_comm _ _ _
  have hcancel := (mul_le_mul_iff_right₀ hpos).mp hbound
  calc
    ‖u - uₕ‖ ≤ (M * ‖u - vₕ‖) / α :=
      (le_div_iff₀ hα).2 (by simpa only [mul_comm α] using hcancel)
    _ = (M / α) * ‖u - vₕ‖ := by rw [div_mul_eq_mul_div]

/-- **Céa's lemma**: the Galerkin error is at most `M / α` times the best approximation error,
where `M` bounds the operator norm and `α` is a positive coercivity constant. -/
theorem norm_sub_le_mul_infDist_of_bound (hcont : ‖B‖ ≤ M) (hα : 0 < α)
    (hcoer : ∀ v, α * ‖v‖ * ‖v‖ ≤ B v v) (huₕ : uₕ ∈ K)
    (horth : ∀ v ∈ K, B (u - uₕ) v = 0) :
    ‖u - uₕ‖ ≤ (M / α) * Metric.infDist u (K : Set E) := by
  have hM : 0 ≤ M := (norm_nonneg B).trans hcont
  refine ((Metric.isGLB_infDist (x := u) (s := (K : Set E)) ⟨0, K.zero_mem⟩).mul_left
    (div_nonneg hM hα.le)).2 ?_
  rintro _ ⟨_, ⟨vₕ, hvₕ, rfl⟩, rfl⟩
  simpa only [dist_eq_norm] using
    B.norm_sub_le_mul_norm_sub_of_bound hcont hα hcoer huₕ horth hvₕ

/-- **Céa's lemma** with the operator norm as continuity constant. -/
theorem norm_sub_le_mul_infDist (hα : 0 < α)
    (hcoer : ∀ v, α * ‖v‖ * ‖v‖ ≤ B v v) (huₕ : uₕ ∈ K)
    (horth : ∀ v ∈ K, B (u - uₕ) v = 0) :
    ‖u - uₕ‖ ≤ (‖B‖ / α) * Metric.infDist u (K : Set E) :=
  B.norm_sub_le_mul_infDist_of_bound le_rfl hα hcoer huₕ horth

end ContinuousLinearMap

/-- A coercive continuous bilinear form has a uniform Galerkin quasi-optimality constant,
independent of the subspace and the exact and approximate solutions. -/
theorem IsCoercive.exists_norm_sub_le_mul_infDist {B : E →L[ℝ] E →L[ℝ] ℝ}
    (hcoer : IsCoercive B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (K : Submodule ℝ E) (u uₕ : E), uₕ ∈ K →
      (∀ v ∈ K, B (u - uₕ) v = 0) → ‖u - uₕ‖ ≤ C * Metric.infDist u (K : Set E) := by
  obtain ⟨α, hα, hcoer⟩ := hcoer
  refine ⟨‖B‖ / α, div_nonneg (norm_nonneg _) hα.le, ?_⟩
  intro K u uₕ huₕ horth
  exact B.norm_sub_le_mul_infDist hα hcoer huₕ horth
