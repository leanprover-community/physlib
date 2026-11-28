/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Physlib.ProbabilisticTheory.CStarAlgebra.State
public import Physlib.QuantumMechanics.HilbertSpaces.Basic

/-!
# Vector states

The vector state of a ray of a Hilbert space.

## i. Overview

A vector `v` of the Hilbert space `H` defines the positive functional `A ↦ ⟪v, A v⟫` on the
bounded operators. Dividing by `‖v‖²` normalizes it to a state. This state only depends on the ray
through `v`. Different rays give different states.

## ii. Key results

- `QuantumMechanics.vectorFunctional` : the vector functional `A ↦ ⟪v, A v⟫` of a vector.
- `QuantumMechanics.vectorState` : the vector state of a ray.
- `QuantumMechanics.extend_vectorState_mk` : the vector state of `v` sends `A` to
  `⟪v, A v⟫ / ‖v‖²`.
- `QuantumMechanics.vectorState_inj` : different rays give different vector states.

## iii. Table of contents

- A. Vector states
- B. Projections onto subspaces

## iv. References

* None.

-/

@[expose] public section

open ProbabilisticTheory ContinuousLinearMap Projectivization
open scoped ComplexOrder InnerProductSpace LinearAlgebra.Projectivization

namespace QuantumMechanics

variable? {H : Type*} [QuantumHilbertSpace H] =>
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## A. Vector states -/

/-- The vector functional `A ↦ ⟪v, A v⟫` of a vector `v`. -/
noncomputable def vectorFunctional (v : H) : 𝓑(H) →ₚ[ℂ] ℂ :=
  .mk₀ ((innerSL ℂ v).comp (apply ℂ H v)).toLinearMap
    fun _ hA ↦ (nonneg_iff_isPositive.mp hA).inner_nonneg_right v

/-- The vector state of a ray `p`, the vector functional of a unit vector on `p`. -/
noncomputable def vectorState (p : ℙ ℂ H) : (quantum H).State :=
  (State.complexEquiv 𝓑(H)).symm ⟨vectorFunctional (((‖p.rep‖⁻¹ : ℝ) : ℂ) • p.rep), by
    change ⟪(((‖p.rep‖⁻¹ : ℝ) : ℂ) • p.rep), (1 : 𝓑(H)) (((‖p.rep‖⁻¹ : ℝ) : ℂ) • p.rep)⟫_ℂ = 1
    rw [one_apply_eq_self, inner_self_eq_norm_sq_to_K]
    simp [norm_smul, p.rep_ne_zero]⟩

TODO "Define the vector states of a representation of a C⋆-algebra on a Hilbert space."

/-- The vector state of the ray through `v` sends `A` to `⟪v, A v⟫ / ‖v‖²`. -/
lemma extend_vectorState_mk (v : H) (hv : v ≠ 0) (A : 𝓑(H)) :
    (vectorState (mk ℂ v hv)).extend A = ⟪v, A v⟫_ℂ / ‖v‖ ^ 2 := by
  obtain ⟨t, ht⟩ := (mk_eq_mk_iff' ℂ _ _ (rep_ne_zero _) hv).mp (mk_rep (mk ℂ v hv))
  have ht0 : t ≠ 0 := left_ne_zero_of_smul (ht ▸ rep_ne_zero (mk ℂ v hv))
  have hv' : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  refine (DFunLike.congr_fun
    (congrArg Subtype.val ((State.complexEquiv 𝓑(H)).apply_symm_apply _)) A).trans ?_
  change ⟪(((‖(mk ℂ v hv).rep‖⁻¹ : ℝ) : ℂ) • (mk ℂ v hv).rep),
    A ((((‖(mk ℂ v hv).rep‖⁻¹ : ℝ) : ℂ) • (mk ℂ v hv).rep))⟫_ℂ = _
  rw [← ht, smul_smul, map_smul, inner_smul_left, inner_smul_right, ← mul_assoc,
    Complex.conj_mul', norm_mul, norm_smul, Complex.norm_real, norm_inv,
    Real.norm_of_nonneg (mul_nonneg (norm_nonneg t) (norm_nonneg v))]
  push_cast
  field_simp

/-! ## B. Projections onto subspaces -/

/-- A vector state has value one on the projection onto a closed subspace `K` exactly when its
ray lies in `K`. -/
lemma extend_vectorState_starProjection_eq_one_iff (p : ℙ ℂ H) (K : Submodule ℂ H)
    [K.HasOrthogonalProjection] :
    (vectorState p).extend K.starProjection = 1 ↔ p.submodule ≤ K := by
  induction p using Projectivization.ind with | h v hv => ?_
  have hv' : (‖v‖ : ℂ) ^ 2 ≠ 0 := by simpa using hv
  have hP : K.starProjection (K.starProjection v) = K.starProjection v := by
    simpa using DFunLike.congr_fun K.isIdempotentElem_starProjection.eq v
  have hinner : ⟪v, K.starProjection v⟫_ℂ = (‖K.starProjection v‖ : ℂ) ^ 2 := by
    conv_lhs => rw [← hP]
    rw [← K.inner_starProjection_left_eq_right, inner_self_eq_norm_sq_to_K]
    rfl
  rw [extend_vectorState_mk, submodule_mk, Submodule.span_singleton_le_iff_mem,
    K.mem_iff_norm_starProjection, div_eq_one_iff_eq hv', hinner]
  exact_mod_cast pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero

/-- Different rays give different vector states. -/
lemma vectorState_inj {p q : ℙ ℂ H} : vectorState p = vectorState q ↔ p = q := by
  refine ⟨fun h ↦ submodule_injective (Submodule.eq_of_le_of_finrank_eq ?_
    (by rw [finrank_submodule, finrank_submodule])), congrArg vectorState⟩
  rw [← extend_vectorState_starProjection_eq_one_iff, h]
  exact (extend_vectorState_starProjection_eq_one_iff q _).mpr le_rfl

end QuantumMechanics
