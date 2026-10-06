/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Mathlib.Analysis.Complex.Basic

/-!

# Upgrading a real-linear map to a complex-linear one

## i. Overview

An `ℝ`-linear map between complex vector spaces that commutes with multiplication by `i` is
`ℂ`-linear, since `c = c.re + c.im · i`. Mathlib has the case of a map out of `ℂ`
(`real_linearMap_map_smul_complex`, `ContinuousLinearMap.complexOfReal`); this file treats an
arbitrary domain.

## ii. Key results

- `LinearMap.map_smul_of_commutesI` : the law along one direction.
- `LinearMap.commutesI_of_basis` : commuting with `i` on a `ℂ`-basis suffices.
- `ContinuousLinearMap.complexOfCommutesI` : the resulting continuous `ℂ`-linear map.

## iii. Table of contents

- A. The scalar law
- B. Commuting with `i` on a basis
- C. The complex-linear map

## iv. References

There are no known references for the material in this module.

-/

@[expose] public section

noncomputable section

namespace LinearMap

variable {V E : Type*} [AddCommGroup V] [Module ℝ V] [Module ℂ V] [IsScalarTower ℝ ℂ V]
  [AddCommGroup E] [Module ℝ E] [Module ℂ E] [IsScalarTower ℝ ℂ E]

/-!

## A. The scalar law

-/

/-- An `ℝ`-linear map commuting with `i` along `v` commutes with every complex scalar along `v`. -/
lemma map_smul_of_commutesI (L : V →ₗ[ℝ] E) {v : V}
    (h : L (Complex.I • v) = Complex.I • L v) (c : ℂ) :
    L (c • v) = c • L v := by
  have hV : c • v = c.re • v + c.im • (Complex.I • v) := by
    conv_lhs => rw [← Complex.re_add_im c]
    simp only [add_smul, mul_smul, ← Complex.coe_algebraMap, algebraMap_smul]
  have hE : c • L v = c.re • L v + c.im • (Complex.I • L v) := by
    conv_lhs => rw [← Complex.re_add_im c]
    simp only [add_smul, mul_smul, ← Complex.coe_algebraMap, algebraMap_smul]
  rw [hV, map_add, L.map_smul, L.map_smul, h, hE]

/-!

## B. Commuting with `i` on a basis

-/

/-- An `ℝ`-linear map commuting with `i` on a `ℂ`-basis commutes with `i` everywhere. -/
lemma commutesI_of_basis {ι : Type*} [Fintype ι] (L : V →ₗ[ℝ] E) (b : Module.Basis ι ℂ V)
    (h : ∀ i, L (Complex.I • b i) = Complex.I • L (b i)) (v : V) :
    L (Complex.I • v) = Complex.I • L v := by
  rw [← b.sum_repr v, Finset.smul_sum, map_sum, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul, map_smul_of_commutesI L (h i), map_smul_of_commutesI L (h i), smul_smul,
    mul_comm]

end LinearMap

namespace ContinuousLinearMap

variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

/-!

## C. The complex-linear map

-/

/-- A continuous `ℝ`-linear map commuting with `i`, as a continuous `ℂ`-linear map. -/
def complexOfCommutesI (L : V →L[ℝ] E)
    (h : ∀ v, L (Complex.I • v) = Complex.I • L v) : V →L[ℂ] E where
  toFun := L
  map_add' := L.map_add
  map_smul' c v := LinearMap.map_smul_of_commutesI (L : V →ₗ[ℝ] E) (h v) c
  cont := L.continuous

@[simp]
lemma complexOfCommutesI_apply (L : V →L[ℝ] E)
    (h : ∀ v, L (Complex.I • v) = Complex.I • L v) (v : V) :
    complexOfCommutesI L h v = L v := rfl

end ContinuousLinearMap

end

end
