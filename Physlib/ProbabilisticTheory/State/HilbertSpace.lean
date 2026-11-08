/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Physlib.ProbabilisticTheory.StarAlgebra.State

/-!
# Vector states on a Hilbert space

Unit vectors define states of the operator algebra. Global phases leave these states unchanged.

## i. Overview

A unit vector `ψ` defines the expectation `⟪ψ, x ψ⟫` of an operator `x`. Two unit vectors give
the same state exactly when they differ by a phase. These states are therefore labelled by rays:
nonzero vectors modulo nonzero scalars.

The expectation of the projection onto a unit vector `φ` is `‖⟪φ, ψ⟫‖ ^ 2`. This is the
transition probability. An orthogonal unit vector gives transition operators whose products
have different expectations. The vector state is then not tracial. No dimension bound is needed.

## ii. Key results

- `UnitalPositiveLinearMap.ofVec` : the vector state of a unit vector.
- `UnitalPositiveLinearMap.ofVec_smul` : a phase `c` with `‖c‖ = 1` does not change the vector
  state.
- `UnitalPositiveLinearMap.ofVec_eq_iff` : two unit vectors have the same vector state if and
  only if they differ by a phase.
- `UnitalPositiveLinearMap.ofVec_rankOne` : the transition probability.
- `UnitalPositiveLinearMap.rayState` : the vector state of a point of the projective space.
- `UnitalPositiveLinearMap.rayState_injective` : different rays give different vector states.
- `UnitalPositiveLinearMap.ofVec_eq_rayState` : every vector state is the state of a ray.
- `UnitalPositiveLinearMap.not_isTracial_ofVec` : a vector state is not tracial when a unit vector
  orthogonal to it exists.

## iii. Table of contents

- A. Vector states
  - A.1. Phase invariance and transition probabilities
- B. Vector states and rays
  - B.1. Distinguishing rays
- C. Vector states are not tracial

## iv. References
-/

@[expose] public section

open ComplexOrder InnerProductSpace Projectivization ContinuousLinearMap
open scoped InnerProductSpace

namespace UnitalPositiveLinearMap

/-!
## A. Vector states
-/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ψ φ : H}

/-- The vector state of a unit vector `ψ`: the expectation value of `x` is `⟪ψ, x ψ⟫`. -/
def ofVec (h : ‖ψ‖ = 1) : 𝓢[ℂ, H →L[ℂ] H] where
  toFun x := ⟪ψ, x ψ⟫_ℂ
  map_add' x y := by simp [inner_add_right]
  map_smul' c x := by simp [inner_smul_right]
  monotone' x y hxy := by
    simpa [inner_sub_right] using (le_def.mp hxy).inner_nonneg_right ψ
  map_one' := by simp [h]

@[simp]
lemma ofVec_apply (h : ‖ψ‖ = 1) (x : H →L[ℂ] H) : ofVec h x = ⟪ψ, x ψ⟫_ℂ := rfl

/-!
### A.1. Phase invariance and transition probabilities
-/

/-- A global phase does not change a vector state. -/
lemma ofVec_smul (h : ‖ψ‖ = 1) {c : ℂ} (hc : ‖c‖ = 1) :
    ofVec (ψ := c • ψ) (by simp [norm_smul, h, hc]) = ofVec h := by
  ext x
  simp [inner_smul_left, inner_smul_right, ← mul_assoc, RCLike.mul_conj, hc]

/-- The vector state of `ψ` on the projection `rankOne ℂ φ φ` is `‖⟪φ, ψ⟫‖ ^ 2`. -/
lemma ofVec_rankOne (h : ‖ψ‖ = 1) (φ : H) :
    ofVec h (rankOne ℂ φ φ) = (‖⟪φ, ψ⟫_ℂ‖ ^ 2 : ℝ) := by
  rw [ofVec_apply, rankOne_apply, inner_smul_right, ← inner_conj_symm ψ φ,
    mul_comm, Complex.conj_mul']
  simp

/-- Equal vector states of unit vectors have overlap of norm one. -/
lemma norm_inner_eq_one_of_ofVec_eq (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1)
    (h : ofVec hψ = ofVec hφ) : ‖⟪ψ, φ⟫_ℂ‖ = 1 := by
  apply (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1
  have hsq := DFunLike.congr_fun h.symm (rankOne ℂ ψ ψ)
  rw [ofVec_rankOne, ofVec_rankOne] at hsq
  simpa [inner_self_eq_norm_sq_to_K, hψ, ← Complex.ofReal_pow] using congrArg Complex.re hsq

/-- Two unit vectors have the same vector state if and only if they differ by a phase. -/
lemma ofVec_eq_iff (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) :
    ofVec hψ = ofVec hφ ↔ ∃ c : ℂ, ‖c‖ = 1 ∧ φ = c • ψ := by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨c, hc, rfl⟩ := (norm_inner_eq_norm_iff (𝕜 := ℂ)
      (norm_ne_zero_iff.1 (hψ ▸ one_ne_zero)) (norm_ne_zero_iff.1 (hφ ▸ one_ne_zero))).1
      (by rw [norm_inner_eq_one_of_ofVec_eq hψ hφ h, hψ, hφ, one_mul])
    exact ⟨c, by simpa [norm_smul, hψ] using hφ, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    exact (ofVec_smul hψ hc).symm

/-!
## B. Vector states and rays
-/

/-- The state of a ray: the vector state of a unit vector on it. -/
noncomputable def rayState (p : Projectivization ℂ H) : 𝓢[ℂ, H →L[ℂ] H] :=
  ofVec (norm_smul_inv_norm (𝕜 := ℂ) p.rep_nonzero)

/-- Normalising proportional vectors gives vectors that differ by a phase. -/
lemma exists_phase {v w : H} (a : ℂ) (ha : a ≠ 0) (h : a • w = v) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ (((‖w‖ : ℂ))⁻¹ • w) = c • (((‖v‖ : ℂ))⁻¹ • v) := by
  refine ⟨(‖a‖ : ℂ) / a, by simp [ha], ?_⟩
  subst v
  simp only [norm_smul, Complex.ofReal_mul, mul_inv_rev, smul_smul]
  congr 1
  field_simp

/-- The state of the ray through a nonzero vector is its normalised vector state. -/
lemma rayState_mk (hψ : ψ ≠ 0) :
    rayState (Projectivization.mk ℂ ψ hψ) = ofVec (norm_smul_inv_norm (𝕜 := ℂ) hψ) := by
  obtain ⟨a, ha⟩ := exists_smul_eq_mk_rep ℂ ψ hψ
  exact (ofVec_eq_iff _ _).2 (exists_phase (a : ℂ) a.ne_zero ha)

/-!
### B.1. Distinguishing rays
-/

/-- Different rays give different vector states. -/
lemma rayState_injective : Function.Injective (rayState (H := H)) := by
  intro p q h
  obtain ⟨c, hc, hpq⟩ := (ofVec_eq_iff _ _).1 h
  apply submodule_injective
  rw [Projectivization.submodule_eq, Projectivization.submodule_eq]
  have hc0 : c ≠ 0 := norm_ne_zero_iff.mp (hc ▸ one_ne_zero)
  simpa [Submodule.span_singleton_smul_eq, isUnit_iff_ne_zero, p.rep_nonzero, q.rep_nonzero,
    hc0] using (congrArg (fun v : H => Submodule.span ℂ {v}) hpq).symm

/-- Every vector state is the state of a ray. -/
lemma ofVec_eq_rayState (h : ‖ψ‖ = 1) :
    ofVec h = rayState (Projectivization.mk ℂ ψ (norm_ne_zero_iff.1 (by simp [h]))) := by
  simp [rayState_mk, h]

/-!
## C. Vector states are not tracial
-/

/-- The vector state of `ψ` is not tracial if a unit vector `φ` is orthogonal to `ψ`. -/
lemma not_isTracial_ofVec (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1)
    (horth : ⟪φ, ψ⟫_ℂ = 0) : ¬ (ofVec hψ).IsTracial := by
  intro h
  simpa [ofVec_apply, mul_def, rankOne_apply, inner_smul_right,
    inner_self_eq_norm_sq_to_K, hψ, hφ, horth] using
    h.map_mul_comm (rankOne ℂ ψ φ) (rankOne ℂ φ ψ)

end UnitalPositiveLinearMap
