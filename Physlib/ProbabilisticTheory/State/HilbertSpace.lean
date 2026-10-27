/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Physlib.ProbabilisticTheory.StarAlgebra.State

/-!
# Vector states on a Hilbert space

The pure states of a quantum system are the rays of its Hilbert space.

## i. Overview

The pure states of a quantum system are the rays of its Hilbert space. A ray is a unit vector up
to a phase. The set of rays is the projective space of the Hilbert space.

A unit vector `ψ` gives an expectation value to every operator `x`. This is the vector state of
`ψ`. A global phase changes no expectation value. Two unit vectors have the same vector
state if and only if they differ by a phase. So the vector states are the points of the
projective space.

Take a unit vector `φ`. The projection onto `φ` is a yes-or-no measurement. Its expectation
value in the vector state of `ψ` is the squared modulus of the overlap of `φ` and `ψ`. This is the
transition probability from `ψ` to `φ`.

The trace does not depend on the order of a product. A vector state is not tracial once the space
has a second direction. The two orders of a product of two transition operators give different
values.

All of this holds in any dimension.

## ii. Key results

- `UnitalPositiveLinearMap.ofVec` : the vector state of a unit vector.
- `UnitalPositiveLinearMap.ofVec_smul` : a phase `c` with `‖c‖ = 1` does not change the vector
  state.
- `UnitalPositiveLinearMap.ofVec_eq_iff` : two unit vectors have the same vector state if and
  only if they differ by a phase.
- `UnitalPositiveLinearMap.ofVec_rankOne` : the transition probability.
- `UnitalPositiveLinearMap.rayState` : the pure state of a point of the projective space.
- `UnitalPositiveLinearMap.rayState_injective` : different rays give different pure states.
- `UnitalPositiveLinearMap.ofVec_eq_rayState` : every vector state is the pure state of a ray.
- `UnitalPositiveLinearMap.not_isTracial_ofVec` : a vector state is not tracial when a unit vector
  orthogonal to it exists.

## iii. Table of contents

- A. Vector states
- B. Pure states are the rays
- C. Vector states are not tracial

## iv. References

None.

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

/-- A global phase does not change a vector state. -/
lemma ofVec_smul (h : ‖ψ‖ = 1) {c : ℂ} (hc : ‖c‖ = 1) :
    ofVec (ψ := c • ψ) (by simp [norm_smul, h, hc]) = ofVec h := by
  ext x
  simp [inner_smul_left, inner_smul_right, ← mul_assoc, RCLike.mul_conj, hc]

/-- The vector state of `ψ` on the projection `rankOne ℂ φ φ` is `‖⟪φ, ψ⟫‖ ^ 2`. -/
lemma ofVec_rankOne (h : ‖ψ‖ = 1) (φ : H) :
    ofVec h (rankOne ℂ φ φ) = (‖⟪φ, ψ⟫_ℂ‖ ^ 2 : ℝ) := by
  rw [ofVec_apply]
  simp only [rankOne_apply]
  rw [inner_smul_right, ← inner_conj_symm ψ φ, mul_comm, Complex.conj_mul']
  simp

/-- Equal vector states of unit vectors have overlap of norm one. -/
lemma norm_inner_eq_one_of_ofVec_eq (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1)
    (h : ofVec hψ = ofVec hφ) : ‖⟪ψ, φ⟫_ℂ‖ = 1 := by
  have h1 := DFunLike.congr_fun h (rankOne ℂ φ φ)
  simp only [ofVec_apply, rankOne_apply, inner_smul_right, inner_self_eq_norm_sq_to_K, hφ] at h1
  rw [← inner_conj_symm φ ψ, Complex.conj_mul'] at h1
  refine (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 ?_
  exact_mod_cast (by simpa using h1 : (‖⟪ψ, φ⟫_ℂ‖ : ℂ) ^ 2 = 1)

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

## B. Pure states are the rays

-/

/-- The pure state of a ray: the vector state of a unit vector on it. -/
noncomputable def rayState (p : Projectivization ℂ H) : 𝓢[ℂ, H →L[ℂ] H] :=
  ofVec (norm_smul_inv_norm (𝕜 := ℂ) p.rep_nonzero)

/-- Normalising two proportional nonzero vectors gives vectors that differ by a phase. -/
lemma exists_phase {v w : H} (a : ℂ) (ha : a ≠ 0) (hw : w ≠ 0) (h : a • w = v) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ (((‖w‖ : ℂ))⁻¹ • w) = c • (((‖v‖ : ℂ))⁻¹ • v) := by
  refine ⟨(‖a‖ : ℂ) / a, by simp [ha], ?_⟩
  subst h
  have hw0 : (‖w‖ : ℂ) ≠ 0 := by simpa using hw
  have ha0 : (‖a‖ : ℂ) ≠ 0 := by simpa using ha
  rw [norm_smul, smul_smul, smul_smul]
  congr 1
  push_cast
  field_simp

/-- The pure state of the ray through a nonzero vector is its vector state. -/
lemma rayState_mk (hψ : ψ ≠ 0) :
    rayState (Projectivization.mk ℂ ψ hψ) = ofVec (norm_smul_inv_norm (𝕜 := ℂ) hψ) := by
  obtain ⟨a, ha⟩ := (mk_eq_mk_iff ℂ _ _
    (Projectivization.mk ℂ ψ hψ).rep_nonzero hψ).1
    (mk_rep (Projectivization.mk ℂ ψ hψ))
  exact (ofVec_eq_iff _ _).2 (exists_phase (a : ℂ) a.ne_zero hψ ha)

/-- Different rays give different pure states. -/
lemma rayState_injective : Function.Injective (rayState (H := H)) := by
  intro p q h
  obtain ⟨c, hc, hpq⟩ := (ofVec_eq_iff _ _).1 h
  have hc0 : c ≠ 0 := norm_ne_zero_iff.1 (by simp [hc])
  have hP : ((‖p.rep‖ : ℂ)) ≠ 0 := by simpa using p.rep_nonzero
  have hQ : ((‖q.rep‖ : ℂ)) ≠ 0 := by simpa using q.rep_nonzero
  have hq : q.rep = ((‖q.rep‖ : ℂ) * c * (‖p.rep‖ : ℂ)⁻¹) • p.rep := by
    rw [mul_smul, mul_smul, ← inv_smul_eq_iff₀ hQ]
    exact hpq
  rw [← mk_rep p, ← mk_rep q]
  exact ((mk_eq_mk_iff ℂ _ _ q.rep_nonzero p.rep_nonzero).2
    ⟨Units.mk0 _ (by simp [hc0, hP, hQ]), hq.symm⟩).symm

/-- Every vector state is the pure state of a ray. -/
lemma ofVec_eq_rayState (h : ‖ψ‖ = 1) :
    ofVec h = rayState (Projectivization.mk ℂ ψ (norm_ne_zero_iff.1 (by simp [h]))) := by
  rw [rayState_mk]
  refine (ofVec_eq_iff _ _).2 ⟨1, by simp, by simp [h]⟩

/-!

## C. Vector states are not tracial

-/

/-- The vector state of `ψ` is not tracial if a unit vector `φ` is orthogonal to `ψ`. -/
lemma not_isTracial_ofVec [CompleteSpace H] (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1)
    (horth : ⟪φ, ψ⟫_ℂ = 0) : ¬ (ofVec hψ).IsTracial := by
  intro h
  have h1 := h (rankOne ℂ ψ φ) (rankOne ℂ φ ψ)
  change ofVec hψ (rankOne ℂ ψ φ * rankOne ℂ φ ψ) = ofVec hψ (rankOne ℂ φ ψ * rankOne ℂ ψ φ)
    at h1
  simp only [mul_def, rankOne_comp_rankOne, map_smul, ofVec_rankOne hψ,
    inner_self_eq_norm_sq_to_K, hφ, hψ, horth] at h1
  simp at h1

end UnitalPositiveLinearMap
