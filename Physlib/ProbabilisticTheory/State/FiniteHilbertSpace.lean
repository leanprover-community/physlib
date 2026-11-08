/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Analysis.InnerProductSpace.Trace
public import Physlib.ProbabilisticTheory.State.HilbertSpace

/-!
# Density operator states of a finite-dimensional Hilbert space

Density operators define mixtures of vector states.

## i. Overview

A density operator `ρ` is positive and has trace one. It assigns the expectation `Tr (x ρ)` to
an operator `x`. A rank-one projection gives a vector state. The spectral theorem expresses any
density state as a mixture of vector states: its eigenvalues are nonnegative and sum to one.

The identity divided by the dimension gives the maximally mixed state. It is the uniform mixture
in any orthonormal basis. Its expectations are traces divided by the dimension. It is tracial.
This file treats finite-dimensional spaces. Infinite dimensions require trace-class operators.

## ii. Key results

- `UnitalPositiveLinearMap.ofDensity` : the state of a density operator.
- `UnitalPositiveLinearMap.ofVec_eq_ofDensity` : the vector state is the state of the projection.
- `UnitalPositiveLinearMap.exists_ofDensity_eq_sum` : every density state is a mixture of vector
  states.
- `UnitalPositiveLinearMap.maximallyMixed` : the maximally mixed state.
- `UnitalPositiveLinearMap.maximallyMixed_eq_sum` : it is the uniform mixture of the vector states
  of an orthonormal basis.
- `UnitalPositiveLinearMap.maximallyMixed_apply` : its expectation value is the trace over the
  dimension.
- `UnitalPositiveLinearMap.maximallyMixed_isTracial` : the maximally mixed state is tracial.

## iii. Table of contents

- A. Density operators and mixtures
  - A.1. Spectral mixtures
- B. The maximally mixed state
  - B.1. Uniform mixtures and traciality

## iv. References
-/

@[expose] public section

open ComplexOrder InnerProductSpace ContinuousLinearMap
open scoped InnerProductSpace

namespace UnitalPositiveLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ψ : H}
  [FiniteDimensional ℂ H]

/-!
## A. Density operators and mixtures
-/

/-- A finite-dimensional inner product space is complete. -/
local instance : CompleteSpace H := FiniteDimensional.complete ℂ H

/-- The trace of a product of two positive operators is nonnegative. -/
lemma trace_mul_nonneg {ρ x : H →L[ℂ] H} (hρ : 0 ≤ ρ) (hx : 0 ≤ x) :
    0 ≤ ((x * ρ : H →L[ℂ] H) : H →ₗ[ℂ] H).trace ℂ H := by
  obtain ⟨m, u, rfl⟩ := isPositive_iff_eq_sum_rankOne.mp
    (nonneg_iff_isPositive.mp hρ)
  simp only [Finset.mul_sum, toLinearMap_sum, map_sum,
    mul_def, comp_rankOne, trace_rankOne]
  exact Finset.sum_nonneg fun i _ =>
    (nonneg_iff_isPositive.mp hx).inner_nonneg_right (u i)

/-- The state of a density operator `ρ`: the expectation value of `x` is `Tr (x ρ)`. -/
noncomputable def ofDensity {ρ : H →L[ℂ] H} (hρ : 0 ≤ ρ)
    (htr : (ρ : H →ₗ[ℂ] H).trace ℂ H = 1) : 𝓢[ℂ, H →L[ℂ] H] :=
  .ofLinearMap
    { toFun x := ((x * ρ : H →L[ℂ] H) : H →ₗ[ℂ] H).trace ℂ H
      map_add' x y := by simp [add_mul]
      map_smul' c x := by simp }
    (fun x hx => trace_mul_nonneg hρ hx) (by simpa using htr)

@[simp]
lemma ofDensity_apply {ρ : H →L[ℂ] H} (hρ : 0 ≤ ρ) (htr : (ρ : H →ₗ[ℂ] H).trace ℂ H = 1)
    (x : H →L[ℂ] H) :
    ofDensity hρ htr x = ((x * ρ : H →L[ℂ] H) : H →ₗ[ℂ] H).trace ℂ H := rfl

/-- The vector state of a unit vector is the state of the projection onto it. -/
lemma ofVec_eq_ofDensity (h : ‖ψ‖ = 1) :
    ofVec h = ofDensity (nonneg_iff_isPositive.mpr (isPositive_rankOne_self ψ))
      (by simp [trace_rankOne, inner_self_eq_norm_sq_to_K, h]) := by
  ext x
  simp [mul_def, comp_rankOne, trace_rankOne]

/-!
### A.1. Spectral mixtures
-/

/-- A density operator is a sum of projections `|u⟩⟨u|`. The squared norms add up to one. -/
lemma exists_eq_sum_rankOne {ρ : H →L[ℂ] H} (hρ : 0 ≤ ρ) (htr : (ρ : H →ₗ[ℂ] H).trace ℂ H = 1) :
    ∃ (m : ℕ) (u : Fin m → H), ρ = ∑ i, rankOne ℂ (u i) (u i) ∧ ∑ i, ‖u i‖ ^ 2 = 1 := by
  obtain ⟨m, u, hu⟩ := isPositive_iff_eq_sum_rankOne.mp
    (nonneg_iff_isPositive.mp hρ)
  refine ⟨m, u, hu, ?_⟩
  exact_mod_cast (by simpa [hu, trace_rankOne, inner_self_eq_norm_sq_to_K] using htr :
    ∑ i, (‖u i‖ : ℂ) ^ 2 = 1)

/-- Every density state is a mixture of vector states. -/
lemma exists_ofDensity_eq_sum {ρ : H →L[ℂ] H} (hρ : 0 ≤ ρ)
    (htr : (ρ : H →ₗ[ℂ] H).trace ℂ H = 1) :
    ∃ (m : ℕ) (p : Fin m → ℝ) (v : Fin m → H) (hv : ∀ i, ‖v i‖ = 1),
      (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1 ∧
        ∀ x, ofDensity hρ htr x = ∑ i, (p i : ℂ) * ofVec (hv i) x := by
  let hpos := nonneg_iff_isPositive.mp hρ
  let b := hpos.isSymmetric.eigenvectorBasis rfl
  refine ⟨Module.finrank ℂ H, hpos.isSymmetric.eigenvalues rfl, b,
    b.orthonormal.norm_eq_one, hpos.toLinearMap.nonneg_eigenvalues rfl, ?_, fun x => ?_⟩
  · rw [← hpos.isSymmetric.re_trace_eq_sum_eigenvalues rfl, htr]
    rfl
  · rw [ofDensity_apply, LinearMap.trace_eq_sum_inner _ b]
    change ∑ i, ⟪b i, x ((ρ : H →ₗ[ℂ] H) (b i))⟫_ℂ = _
    simp only [b, hpos.isSymmetric.apply_eigenvectorBasis, map_smul, inner_smul_right,
      ofVec_apply]
    rfl

/-!
## B. The maximally mixed state
-/

/-- The operator `1 / n`, where `n` is the dimension of `H`. -/
noncomputable def maximallyMixedDensity : H →L[ℂ] H :=
  (Module.finrank ℂ H : ℂ)⁻¹ • 1

lemma maximallyMixedDensity_nonneg : 0 ≤ (maximallyMixedDensity : H →L[ℂ] H) :=
  smul_nonneg (by positivity) zero_le_one

/-- The maximally mixed density operator has trace one. -/
lemma trace_maximallyMixedDensity [Nontrivial H] :
    ((maximallyMixedDensity : H →L[ℂ] H) : H →ₗ[ℂ] H).trace ℂ H = 1 := by
  have : (Module.finrank ℂ H : ℂ) ≠ 0 := by simp [Module.finrank_pos.ne']
  simp [maximallyMixedDensity, this]

/-- The maximally mixed state. It is the state of the density operator `1 / n`. -/
noncomputable def maximallyMixed [Nontrivial H] : 𝓢[ℂ, H →L[ℂ] H] :=
  .ofDensity maximallyMixedDensity_nonneg trace_maximallyMixedDensity

@[simp] lemma maximallyMixed_apply [Nontrivial H] (x : H →L[ℂ] H) :
    maximallyMixed (H := H) x = (Module.finrank ℂ H : ℂ)⁻¹ * (x : H →ₗ[ℂ] H).trace ℂ H := by
  simp [maximallyMixed, maximallyMixedDensity]

/-!
### B.1. Uniform mixtures and traciality
-/

/-- The maximally mixed state is the uniform mixture of the vector states of an orthonormal
basis. -/
lemma maximallyMixed_eq_sum [Nontrivial H] {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ H) (x : H →L[ℂ] H) :
    maximallyMixed (H := H) x =
      (Fintype.card ι : ℂ)⁻¹ * ∑ i, ofVec (b.orthonormal.norm_eq_one i) x := by
  rw [maximallyMixed_apply, LinearMap.trace_eq_sum_inner _ b,
    Module.finrank_eq_card_basis b.toBasis]
  simp

/-- Every rank-one projection has the same maximally mixed expectation. -/
lemma maximallyMixed_rankOne [Nontrivial H] (h : ‖ψ‖ = 1) :
    maximallyMixed (H := H) (rankOne ℂ ψ ψ) = (Module.finrank ℂ H : ℂ)⁻¹ := by
  rw [maximallyMixed_apply, trace_rankOne, inner_self_eq_norm_sq_to_K, h]
  simp

/-- The maximally mixed state does not depend on the order of a product. -/
lemma maximallyMixed_isTracial [Nontrivial H] : (maximallyMixed (H := H)).IsTracial := by
  intro x y
  change maximallyMixed (x * y) = maximallyMixed (y * x)
  simp [maximallyMixed_apply, LinearMap.trace_mul_comm]

end UnitalPositiveLinearMap
