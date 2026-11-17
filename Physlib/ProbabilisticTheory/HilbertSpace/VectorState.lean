/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Physlib.ProbabilisticTheory.HilbertSpace.Projection
public import Physlib.ProbabilisticTheory.State.Convex

/-!
# Vector states

Every ray of a Hilbert space is a pure state of its bounded operators.

## i. Overview

A nonzero vector `v` of the Hilbert space `H` gives the operator `A` the expectation value
`⟪v, A v⟫ / ‖v‖²`. A nonzero multiple of `v` gives the same expectation values. So the state
depends only on the ray `p` through `v`. This is the vector state of `p`.

A subspace `K` of `H` is a yes-no measurement. The vector state of `p` answers yes with
certainty exactly when `p` lies in `K`.

The measurement of `p` itself characterizes its state. A state certain of the answer yes is
the vector state of `p`. So the vector state is pure. Different rays give different states.
Thus the rays of `H` embed into the pure states.

## ii. Key results

- `UnitalPositiveLinearMap.ofVec` : the state of a nonzero vector.
- `Projectivization.vectorState` : the vector state of a ray.
- `Projectivization.vectorState_mk_apply` : the expectation value `⟪v, A v⟫ / ‖v‖²`.
- `Projectivization.vectorState_toEffect_eq_one_iff` : a vector state is certain of a subspace
  exactly when its ray lies in it.
- `Projectivization.eq_vectorState_iff` : certainty of its own ray characterizes a vector state.
- `Projectivization.isPure_vectorState` : vector states are pure.
- `Projectivization.toPureState` : the rays embed into the pure states.

## iii. Table of contents

- A. Vector states
- B. Certainty of a subspace
- C. Pure states

## iv. References

- [ref: hall2013quantum]
-/

@[expose] public section

open scoped ComplexOrder InnerProductSpace LinearAlgebra.Projectivization
open ContinuousLinearMap ProbabilisticTheory

/-! ## A. Vector states -/

namespace UnitalPositiveLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The state of a nonzero vector `v`. It gives the operator `A` the expectation value
`⟪v, A v⟫ / ‖v‖²`. -/
noncomputable def ofVec (v : {v : H // v ≠ 0}) : 𝓢[ℂ, 𝓑(H)] :=
  .ofLinearMap ((((‖(v : H)‖ ^ 2)⁻¹ : ℝ) : ℂ) •
      ((innerSL ℂ (v : H)).comp (ContinuousLinearMap.apply ℂ H (v : H))).toLinearMap)
    (by
      intro A hA
      exact mul_nonneg (Complex.zero_le_real.mpr (by positivity))
        ((nonneg_iff_isPositive.mp hA).inner_nonneg_right (v : H)))
    (by
      have hv : ‖(v : H)‖ ≠ 0 := norm_ne_zero_iff.mpr v.2
      simp [inner_self_eq_norm_sq_to_K]
      field_simp)

lemma ofVec_apply (v : {v : H // v ≠ 0}) (A : 𝓑(H)) :
    ofVec v A = ⟪(v : H), A v⟫_ℂ / ‖(v : H)‖ ^ 2 := by
  change (((‖(v : H)‖ ^ 2)⁻¹ : ℝ) : ℂ) * ⟪(v : H), A v⟫_ℂ = _
  push_cast
  rw [div_eq_inv_mul]

/-- A nonzero multiple of a vector has the same state. -/
lemma ofVec_eq_of_eq_smul (v w : {v : H // v ≠ 0}) (t : ℂ) (h : (v : H) = t • (w : H)) :
    ofVec v = ofVec w := by
  have ht : t ≠ 0 := by
    rintro rfl
    exact v.2 (by simpa using h)
  have hw : ‖(w : H)‖ ≠ 0 := norm_ne_zero_iff.mpr w.2
  refine DFunLike.ext _ _ ?_
  intro A
  rw [ofVec_apply, ofVec_apply, h, inner_smul_left, map_smul, inner_smul_right, norm_smul,
    ← mul_assoc, Complex.conj_mul']
  push_cast
  field_simp

end UnitalPositiveLinearMap

namespace Projectivization

open UnitalPositiveLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The vector state of a ray. -/
noncomputable def vectorState (p : ℙ ℂ H) : 𝓢[ℂ, 𝓑(H)] :=
  Projectivization.lift ofVec ofVec_eq_of_eq_smul p

/-- Every nonzero vector on the ray gives the expectation value `⟪v, A v⟫ / ‖v‖²`. -/
lemma vectorState_mk_apply (v : H) (hv : v ≠ 0) (A : 𝓑(H)) :
    (mk ℂ v hv).vectorState A = ⟪v, A v⟫_ℂ / ‖v‖ ^ 2 :=
  ofVec_apply ⟨v, hv⟩ A

/-! ## B. Certainty of a subspace -/

/-- A vector state gives the projection onto `K` the expectation one exactly when its ray lies
in `K`. -/
lemma vectorState_starProjection_eq_one_iff (p : ℙ ℂ H) (K : Submodule ℂ H)
    [K.HasOrthogonalProjection] : p.vectorState K.starProjection = 1 ↔ p.submodule ≤ K := by
  refine Projectivization.ind ?_ p
  intro v hv
  have hv' : (‖v‖ : ℂ) ^ 2 ≠ 0 := by simpa using hv
  have hP : K.starProjection (K.starProjection v) = K.starProjection v := by
    simpa using DFunLike.congr_fun K.isIdempotentElem_starProjection.eq v
  have hinner : ⟪v, K.starProjection v⟫_ℂ = (‖K.starProjection v‖ : ℂ) ^ 2 := by
    conv_lhs => rw [← hP]
    rw [← K.inner_starProjection_left_eq_right, inner_self_eq_norm_sq_to_K]
    rfl
  rw [vectorState_mk_apply, submodule_mk, Submodule.span_singleton_le_iff_mem,
    K.mem_iff_norm_starProjection, div_eq_one_iff_eq hv', hinner]
  exact_mod_cast pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero

/-- Compression by the projection onto a ray multiplies by the expectation value. -/
lemma starProjection_mul_mul_starProjection (p : ℙ ℂ H) (A : 𝓑(H)) :
    p.submodule.starProjection * A * p.submodule.starProjection =
      p.vectorState A • p.submodule.starProjection := by
  refine Projectivization.ind ?_ p
  intro v hv
  ext w
  simp [submodule_mk, vectorState_mk_apply, Submodule.starProjection_singleton, smul_smul]
  congr 1
  ring

/-- A vector state is certain of a subspace exactly when its ray lies in the subspace. -/
lemma vectorState_toEffect_eq_one_iff [CompleteSpace H] (p : ℙ ℂ H) (K : Submodule ℂ H)
    [K.HasOrthogonalProjection] :
    p.vectorState.onObservables K.toEffect = 1 ↔ p.submodule ≤ K := by
  rw [← Complex.ofReal_eq_one, coe_onObservables_apply]
  exact p.vectorState_starProjection_eq_one_iff K

/-- Certainty of its own ray characterizes a vector state. -/
lemma eq_vectorState_iff [CompleteSpace H] (p : ℙ ℂ H) (φ : 𝓢[ℝ, Observable 𝓑(H)]) :
    φ = p.vectorState.onObservables ↔ φ p.submodule.toEffect = 1 := by
  refine ⟨?_, ?_⟩
  · rintro rfl
    exact (p.vectorState_toEffect_eq_one_iff _).mpr le_rfl
  · intro hφ
    have hω : ofObservables φ p.submodule.starProjection = 1 := by
      rw [← Submodule.coe_toEffect, ofObservables_apply, hφ, Complex.ofReal_one]
    have h : ofObservables φ = p.vectorState := by
      refine DFunLike.ext _ _ ?_
      intro A
      rw [(ofObservables φ).apply_eq_apply_mul_mul_of_apply_eq_one isStarProjection_starProjection
        hω, starProjection_mul_mul_starProjection, map_smul, hω, smul_eq_mul, mul_one]
    rw [← h]
    exact (observablesEquiv.apply_symm_apply φ).symm

/-! ## C. Pure states -/

/-- Vector states are pure. -/
lemma isPure_vectorState [CompleteSpace H] (p : ℙ ℂ H) : p.vectorState.onObservables.IsPure := by
  refine isPure_of_apply_eq_one_iff p.submodule.toEffect.2.2 ?_
  intro φ
  exact (p.eq_vectorState_iff φ).symm

/-- Different rays give different vector states. -/
lemma vectorState_injective : Function.Injective (vectorState (H := H)) := by
  intro p q h
  have hle : p.submodule ≤ q.submodule := (p.vectorState_starProjection_eq_one_iff _).mp
    (by rw [h]; exact (q.vectorState_starProjection_eq_one_iff _).mpr le_rfl)
  exact submodule_injective
    (Submodule.eq_of_le_of_finrank_eq hle (by rw [finrank_submodule, finrank_submodule]))

/-- The rays of a Hilbert space embed into the pure states of its observables. -/
noncomputable def toPureState [CompleteSpace H] :
    ℙ ℂ H ↪ {ω : 𝓢[ℝ, Observable 𝓑(H)] // ω.IsPure} where
  toFun p := ⟨p.vectorState.onObservables, p.isPure_vectorState⟩
  inj' _ _ h := vectorState_injective (observablesEquiv.injective (congrArg Subtype.val h))

end Projectivization
