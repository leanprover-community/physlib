/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.InnerProductSpace.Trace
public import Physlib.ProbabilisticTheory.State.HilbertSpace

/-!
# Density operator states of a finite-dimensional Hilbert space

Every mixed state is a mixture of pure states.

## i. Overview

A mixed state is described by a density operator `ρ`: a positive operator of trace one. The
expectation value of an operator is the trace of its product with `ρ`. The projection onto a
unit vector is a density operator of rank one. Its state is the vector state. Every density
operator is a sum of such projections with positive weights that add up to one. So every mixed
state is a mixture of pure states. This is the spectral decomposition.

The trace is needed here. So this file treats finite-dimensional Hilbert spaces. An
infinite-dimensional system needs trace-class operators.

The identity divided by the dimension is a density operator. Its state is the maximally mixed
state. It is the uniform mixture of the vector states of any orthonormal basis. The expectation
value of an operator is its trace divided by the dimension.

The trace does not depend on the order of a product. So the maximally mixed state is tracial.

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
- B. The maximally mixed state

## iv. References

None.

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
  simp [mul_def, comp_rankOne,
    trace_rankOne]

/-- A density operator is a sum of projections `|u⟩⟨u|`. The squared norms add up to one. -/
lemma exists_eq_sum_rankOne {ρ : H →L[ℂ] H} (hρ : 0 ≤ ρ) (htr : (ρ : H →ₗ[ℂ] H).trace ℂ H = 1) :
    ∃ (m : ℕ) (u : Fin m → H), ρ = ∑ i, rankOne ℂ (u i) (u i) ∧ ∑ i, ‖u i‖ ^ 2 = 1 := by
  obtain ⟨m, u, hu⟩ := isPositive_iff_eq_sum_rankOne.mp
    (nonneg_iff_isPositive.mp hρ)
  refine ⟨m, u, hu, ?_⟩
  subst hu
  simp only [toLinearMap_sum, map_sum, trace_rankOne,
    inner_self_eq_norm_sq_to_K] at htr
  have := congrArg Complex.re htr
  simpa [Complex.re_sum, ← Complex.ofReal_pow] using this

/-- Every density state is a mixture of vector states. -/
lemma exists_ofDensity_eq_sum {ρ : H →L[ℂ] H} (hρ : 0 ≤ ρ)
    (htr : (ρ : H →ₗ[ℂ] H).trace ℂ H = 1) :
    ∃ (m : ℕ) (p : Fin m → ℝ) (v : Fin m → H) (hv : ∀ i, ‖v i‖ = 1),
      (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1 ∧
        ∀ x, ofDensity hρ htr x = ∑ i, (p i : ℂ) * ofVec (hv i) x := by
  obtain ⟨m, u, hu, hsum⟩ := exists_eq_sum_rankOne hρ htr
  obtain ⟨i₀, hi₀⟩ : ∃ i, u i ≠ 0 := by
    by_contra h
    have h' : ∀ i, u i = 0 := by simpa using h
    simp [h'] at hsum
  classical
  let v : Fin m → H := fun i =>
    if u i = 0 then ((‖u i₀‖ : ℂ))⁻¹ • u i₀ else ((‖u i‖ : ℂ))⁻¹ • u i
  have hv : ∀ i, ‖v i‖ = 1 := by
    intro i
    by_cases h : u i = 0
    · simpa [v, h] using norm_smul_inv_norm (𝕜 := ℂ) hi₀
    · simpa [v, h] using norm_smul_inv_norm (𝕜 := ℂ) h
  refine ⟨m, fun i => ‖u i‖ ^ 2, v, hv, fun i => by positivity, hsum, fun x => ?_⟩
  subst hu
  rw [ofDensity_apply]
  simp only [Finset.mul_sum, toLinearMap_sum, map_sum,
    mul_def, comp_rankOne, trace_rankOne]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : u i = 0
  · simp [h]
  · have hn : (‖u i‖ : ℂ) ≠ 0 := by simpa using h
    simp only [ofVec_apply, v, h, ite_false, inner_smul_left, inner_smul_right, map_smul]
    simp [Complex.ofReal_pow]
    field_simp

/-!

## B. The maximally mixed state

-/

/-- The operator `1 / n`, where `n` is the dimension of `H`. -/
noncomputable def maximallyMixedDensity : H →L[ℂ] H :=
  (Module.finrank ℂ H : ℂ)⁻¹ • 1

lemma maximallyMixedDensity_nonneg : 0 ≤ (maximallyMixedDensity : H →L[ℂ] H) :=
  smul_nonneg (by positivity) zero_le_one

variable [Nontrivial H]

lemma trace_maximallyMixedDensity :
    ((maximallyMixedDensity : H →L[ℂ] H) : H →ₗ[ℂ] H).trace ℂ H = 1 := by
  have : (Module.finrank ℂ H : ℂ) ≠ 0 := by simp [Module.finrank_pos.ne']
  simp [maximallyMixedDensity, this]

/-- The maximally mixed state. It is the state of the density operator `1 / n`. -/
noncomputable def maximallyMixed : 𝓢[ℂ, H →L[ℂ] H] :=
  .ofDensity maximallyMixedDensity_nonneg trace_maximallyMixedDensity

@[simp] lemma maximallyMixed_apply (x : H →L[ℂ] H) :
    maximallyMixed (H := H) x = (Module.finrank ℂ H : ℂ)⁻¹ * (x : H →ₗ[ℂ] H).trace ℂ H := by
  simp [maximallyMixed, maximallyMixedDensity]

/-- The maximally mixed state is the uniform mixture of the vector states of an orthonormal
basis. -/
lemma maximallyMixed_eq_sum {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ H) (x : H →L[ℂ] H) :
    maximallyMixed (H := H) x =
      (Fintype.card ι : ℂ)⁻¹ * ∑ i, ofVec (b.orthonormal.norm_eq_one i) x := by
  rw [maximallyMixed_apply, LinearMap.trace_eq_sum_inner _ b,
    Module.finrank_eq_card_basis b.toBasis]
  simp

lemma maximallyMixed_rankOne (h : ‖ψ‖ = 1) :
    maximallyMixed (H := H) (rankOne ℂ ψ ψ) = (Module.finrank ℂ H : ℂ)⁻¹ := by
  rw [maximallyMixed_apply, trace_rankOne, inner_self_eq_norm_sq_to_K, h]
  simp

lemma maximallyMixed_isTracial : (maximallyMixed (H := H)).IsTracial := by
  intro x y
  change maximallyMixed (x * y) = maximallyMixed (y * x)
  simp [maximallyMixed_apply, LinearMap.trace_mul_comm]

end UnitalPositiveLinearMap
