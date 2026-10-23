/-
Copyright (c) 2026 brent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: brent
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import PhyslibAlpha.ProbabilisticTheory.CStarAlgebra.OrderUnit
public import PhyslibAlpha.ProbabilisticTheory.HilbertSpace.State.Vector
public import PhyslibAlpha.ProbabilisticTheory.Measurement.Finite
public import PhyslibAlpha.ProbabilisticTheory.StarAlgebra.Statistics

/-!

# Measurements in an orthonormal family

The measurement of a quantum system on a complex Hilbert space in a finite orthonormal family.

## i. Overview

Let `b x`, for `x` in a finite type `X`, be orthonormal vectors of a complex Hilbert space `H`.
The rank-one projections `|b x⟩⟨b x|` are effects, and by Bessel's inequality their sum is at most
`1`. Adding the remainder `1 - ∑ x, |b x⟩⟨b x|` to the effect of a chosen outcome `x₀` gives a
measurement with outcomes `X`. On a unit vector `φ`, the outcome `x` has probability
`‖⟪b x, φ⟫‖ ^ 2`, plus `1 - ∑ y, ‖⟪b y, φ⟫‖ ^ 2` when `x = x₀`. In particular, if `φ` lies in the
span of the `b x`, the outcome `x` has probability `‖⟪b x, φ⟫‖ ^ 2`.

## ii. Key results

- `rankOneObservable` : the rank-one observable `|v⟩⟨v|`.
- `orthonormalObservable` : the observable of an outcome, `|b x⟩⟨b x|` plus the remainder on `x₀`.
- `sum_orthonormalObservable`, `orthonormalObservable_nonneg` : the outcome observables are
  positive and add up to `1`.
- `Measurement.ofOrthonormal` : the measurement in an orthonormal family.
- `Measurement.expectation_ofOrthonormal_singleton` : the Born rule for this measurement.

## iii. Table of contents

- A. Rank-one observables
- B. The outcome observables
- C. The measurement and its Born rule

## iv. References

* None.

-/

@[expose] public section

namespace ProbabilisticTheory

open InnerProductSpace UnitalPositiveLinearMap
open scoped ComplexOrder

variable {H X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [Fintype X]

/-!

## A. Rank-one observables

-/

/-- `⟪φ, |v⟩⟨v| φ⟫ = ‖⟪v, φ⟫‖ ^ 2`. -/
lemma inner_rankOne_self_apply (v φ : H) :
    ⟪φ, rankOne ℂ v v φ⟫_ℂ = (‖⟪v, φ⟫_ℂ‖ ^ 2 : ℝ) := by
  rw [inner_right_rankOne_apply, ← inner_conj_symm φ v, RCLike.conj_mul]
  norm_cast

/-- `⟪φ, ∑ y, |b y⟩⟨b y| φ⟫ = ∑ y, ‖⟪b y, φ⟫‖ ^ 2`. -/
lemma inner_sum_rankOne_self_apply (b : X → H) (φ : H) :
    ⟪φ, (∑ y, rankOne ℂ (b y) (b y)) φ⟫_ℂ = (∑ y, ‖⟪b y, φ⟫_ℂ‖ ^ 2 : ℝ) := by
  rw [sum_apply, inner_sum, Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun y _ => inner_rankOne_self_apply (b y) φ

/-- By Bessel's inequality, `1 - ∑ y, |b y⟩⟨b y|` is positive for an orthonormal family `b`. -/
lemma isPositive_one_sub_sum_rankOne {b : X → H} (hb : Orthonormal ℂ b) :
    (1 - ∑ y, rankOne ℂ (b y) (b y)).IsPositive := by
  refine (ContinuousLinearMap.isPositive_iff _).2 ⟨?_, fun φ => ?_⟩
  · rw [ContinuousLinearMap.toLinearMap_sub, ContinuousLinearMap.toLinearMap_sum,
      ContinuousLinearMap.toLinearMap_one]
    exact LinearMap.IsSymmetric.one.sub
      (LinearMap.isSymmetric_sum _ fun y _ => (isPositive_rankOne_self (b y)).isSymmetric)
  · rw [← inner_conj_symm, sub_apply, inner_sub_right,
      inner_sum_rankOne_self_apply, one_apply_eq_self, inner_self_eq_norm_sq_to_K]
    norm_cast
    change 0 ≤ starRingEnd ℂ (((‖φ‖ ^ 2 : ℝ) : ℂ) - ((∑ y, ‖⟪b y, φ⟫_ℂ‖ ^ 2 : ℝ) : ℂ))
    rw [← Complex.ofReal_sub, Complex.conj_ofReal, Complex.zero_le_real, sub_nonneg]
    exact hb.sum_inner_products_le φ

variable [CompleteSpace H]

/-- The rank-one observable `|v⟩⟨v|`. -/
noncomputable def rankOneObservable (v : H) : Observable (H →L[ℂ] H) :=
  ⟨rankOne ℂ v v, (isPositive_rankOne_self v).isSelfAdjoint⟩

@[simp]
lemma coe_rankOneObservable (v : H) :
    (rankOneObservable v : H →L[ℂ] H) = rankOne ℂ v v := rfl

/-- The rank-one observable `|v⟩⟨v|` is positive. -/
lemma rankOneObservable_nonneg (v : H) : 0 ≤ rankOneObservable v :=
  ContinuousLinearMap.nonneg_iff_isPositive.2 (isPositive_rankOne_self v)

/-!

## B. The outcome observables

-/

variable [DecidableEq X]

/-- The observable of the outcome `x` in the measurement in the family `b`: `|b x⟩⟨b x|`, plus
the remainder `1 - ∑ y, |b y⟩⟨b y|` when `x = x₀`. -/
noncomputable def orthonormalObservable (b : X → H) (x₀ x : X) : Observable (H →L[ℂ] H) :=
  rankOneObservable (b x) + if x = x₀ then 1 - ∑ y, rankOneObservable (b y) else 0

/-- The operator underlying the observable of the outcome `x`. -/
lemma coe_orthonormalObservable (b : X → H) (x₀ x : X) :
    (orthonormalObservable b x₀ x : H →L[ℂ] H) =
      rankOne ℂ (b x) (b x) + if x = x₀ then 1 - ∑ y, rankOne ℂ (b y) (b y) else 0 := by
  split_ifs with h <;> simp [orthonormalObservable, h]

/-- The outcome observables add up to `1`. -/
lemma sum_orthonormalObservable (b : X → H) (x₀ : X) :
    ∑ x, orthonormalObservable b x₀ x = 1 := by
  simp [orthonormalObservable, Finset.sum_add_distrib]

/-- The outcome observables of an orthonormal family are positive. -/
lemma orthonormalObservable_nonneg {b : X → H} (hb : Orthonormal ℂ b) (x₀ x : X) :
    0 ≤ orthonormalObservable b x₀ x := by
  refine add_nonneg (rankOneObservable_nonneg _) ?_
  split_ifs
  · show (0 : H →L[ℂ] H) ≤ ((1 - ∑ y, rankOneObservable (b y) :
      Observable (H →L[ℂ] H)) : H →L[ℂ] H)
    push_cast
    exact ContinuousLinearMap.nonneg_iff_isPositive.2 (isPositive_one_sub_sum_rankOne hb)
  · exact le_rfl

/-- The outcome effects of the measurement in an orthonormal family. -/
noncomputable def orthonormalEffect {b : X → H} (hb : Orthonormal ℂ b) (x₀ x : X) :
    Effect (Observable (H →L[ℂ] H)) :=
  ⟨orthonormalObservable b x₀ x, orthonormalObservable_nonneg hb x₀ x,
    (Finset.single_le_sum (fun y _ => orthonormalObservable_nonneg hb x₀ y)
      (Finset.mem_univ x)).trans_eq (sum_orthonormalObservable b x₀)⟩

@[simp]
lemma coe_orthonormalEffect {b : X → H} (hb : Orthonormal ℂ b) (x₀ x : X) :
    (orthonormalEffect hb x₀ x : Observable (H →L[ℂ] H)) = orthonormalObservable b x₀ x :=
  rfl

/-!

## C. The measurement and its Born rule

-/

namespace Measurement

variable [MeasurableSpace X]

/-- The measurement in the orthonormal family `b`: the outcome `x` has effect `|b x⟩⟨b x|`, and
the outcome `x₀` also registers the orthogonal complement of the span of the family. -/
noncomputable def ofOrthonormal {b : X → H} (hb : Orthonormal ℂ b) (x₀ : X) :
    Measurement X (Observable (H →L[ℂ] H)) :=
  ofAtoms (orthonormalEffect hb x₀) (sum_orthonormalObservable b x₀)

/-- The outcome `x` of the measurement in an orthonormal family has the observable
`orthonormalObservable b x₀ x`. -/
lemma coe_ofOrthonormal_singleton {b : X → H} (hb : Orthonormal ℂ b) (x₀ x : X)
    (hx : MeasurableSet {x}) :
    (ofOrthonormal hb x₀ {x} hx : Observable (H →L[ℂ] H)) = orthonormalObservable b x₀ x :=
  coe_ofAtoms_singleton _ _ x hx

/-- The Born rule for the measurement in an orthonormal family: on a unit vector `φ`, the
outcome `x` has probability `‖⟪b x, φ⟫‖ ^ 2`, plus `1 - ∑ y, ‖⟪b y, φ⟫‖ ^ 2` when `x = x₀`. -/
lemma expectation_ofOrthonormal_singleton [MeasurableSingletonClass X] {b : X → H}
    (hb : Orthonormal ℂ b) (x₀ : X) {φ : H} (hφ : ‖φ‖ = 1) (x : X) :
    (ofVec hφ)⟨ofOrthonormal hb x₀ {x} (measurableSet_singleton x)⟩ =
      ‖⟪b x, φ⟫_ℂ‖ ^ 2 + if x = x₀ then 1 - ∑ y, ‖⟪b y, φ⟫_ℂ‖ ^ 2 else 0 := by
  apply Complex.ofReal_injective
  rw [← apply_observable_eq_expectation, coe_ofOrthonormal_singleton, ofVec_apply,
    ContinuousLinearMap.smul_def, coe_orthonormalObservable, add_apply, inner_add_right,
    inner_rankOne_self_apply]
  split_ifs
  · rw [sub_apply, inner_sub_right, inner_sum_rankOne_self_apply, one_apply_eq_self,
      inner_self_eq_norm_sq_to_K, hφ]
    push_cast
    ring
  · rw [zero_apply, inner_zero_right, add_zero, add_zero]

end Measurement

end ProbabilisticTheory
