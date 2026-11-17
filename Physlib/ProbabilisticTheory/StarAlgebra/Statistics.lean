/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.ProbabilisticTheory.StarAlgebra.State

/-!
# Covariance and variance of observables

Variance measures the spread of an observable in a state. Covariance measures how two observables
vary together.

## i. Overview

The statistics of an observable depend on the state of the system. Its mean is the expected
measurement outcome. Its variance measures the spread of the outcomes around the mean. Covariance
measures the dependence between two observables. A positive covariance means their outcomes tend to
deviate from their means in the same direction. A negative covariance means opposite deviations.

Quantum observables need not commute. So the covariance uses their symmetric product. This product
is again an observable. For commuting observables it gives the usual covariance of their joint
outcomes. Noncommuting observables have no joint outcomes in general. Their covariance is still a
well-defined quantum statistic.

## ii. Key results

- `UnitalPositiveLinearMap.centered` : an observable with its mean subtracted.
- `UnitalPositiveLinearMap.covariance` : the covariance of two observables.
- `UnitalPositiveLinearMap.variance` : the variance of an observable.
- `UnitalPositiveLinearMap.coe_variance` : the variance is the mean of the squared centered
  observable.
- `UnitalPositiveLinearMap.variance_nonneg` : the variance is nonnegative.

## iii. Table of contents

- A. Centered observables
- B. Covariance and variance

## iv. References

* None.

-/

@[expose] public section

open scoped ComplexOrder ComplexStarModule

namespace UnitalPositiveLinearMap

variable {𝒜 : Type*} [Ring 𝒜] [PartialOrder 𝒜] [StarRing 𝒜] [Algebra ℂ 𝒜] [StarModule ℂ 𝒜]

/-! ## A. Centered observables -/

/-- Subtracts the mean of an observable in the state `ω`. -/
noncomputable def centered (ω : 𝓢[ℝ, Observable 𝒜]) (a : Observable 𝒜) : Observable 𝒜 :=
  a - ω a • 1

/-- A centered observable has zero mean. -/
@[simp]
lemma apply_centered (ω : 𝓢[ℝ, Observable 𝒜]) (a : Observable 𝒜) : ω (ω.centered a) = 0 := by
  simp [centered]

/-- Centering is invariant under constant shifts. -/
@[simp]
lemma centered_add_smul_one (ω : 𝓢[ℝ, Observable 𝒜]) (a : Observable 𝒜) (c : ℝ) :
    ω.centered (a + c • 1) = ω.centered a := by
  simp only [centered, map_add, map_smul, map_one, smul_eq_mul, mul_one]
  module

/-! ## B. Covariance and variance -/

/-- The symmetric covariance of two observables in the state `ω`. -/
noncomputable def covariance (ω : 𝓢[ℝ, Observable 𝒜]) (a b : Observable 𝒜) : ℝ :=
  ω (ℜ ((ω.centered a : 𝒜) * ω.centered b))

/-- The variance of an observable in the state `ω`. -/
noncomputable def variance (ω : 𝓢[ℝ, Observable 𝒜]) (a : Observable 𝒜) : ℝ :=
  ω.covariance a a

/-- Covariance is symmetric. -/
lemma covariance_comm (ω : 𝓢[ℝ, Observable 𝒜]) (a b : Observable 𝒜) :
    ω.covariance a b = ω.covariance b a := by
  have h : ℜ ((ω.centered b : 𝒜) * ω.centered a) = ℜ ((ω.centered a : 𝒜) * ω.centered b) := by
    refine Subtype.ext ?_
    rw [realPart_apply_coe, realPart_apply_coe, star_mul, star_mul, (ω.centered a).2.star_eq,
      (ω.centered b).2.star_eq, add_comm]
  rw [covariance, covariance, h]

/-- Covariance is invariant under constant shifts of the first observable. -/
@[simp]
lemma covariance_add_smul_one_left (ω : 𝓢[ℝ, Observable 𝒜]) (a b : Observable 𝒜) (c : ℝ) :
    ω.covariance (a + c • 1) b = ω.covariance a b := by
  simp only [covariance, centered_add_smul_one]

/-- Covariance is invariant under constant shifts of the second observable. -/
@[simp]
lemma covariance_add_smul_one_right (ω : 𝓢[ℝ, Observable 𝒜]) (a b : Observable 𝒜) (c : ℝ) :
    ω.covariance a (b + c • 1) = ω.covariance a b := by
  simp only [covariance, centered_add_smul_one]

/-- The square of a centered observable is self-adjoint. -/
lemma isSelfAdjoint_centered_mul_self (ω : 𝓢[ℝ, Observable 𝒜]) (a : Observable 𝒜) :
    IsSelfAdjoint ((ω.centered a : 𝒜) * ω.centered a) := by
  rw [isSelfAdjoint_iff, star_mul, (ω.centered a).2.star_eq]

/-- Variance equals the mean of the squared centered observable. -/
lemma coe_variance [StarOrderedRing 𝒜] (ω : 𝓢[ℝ, Observable 𝒜]) (a : Observable 𝒜) :
    (ω.variance a : ℂ) = ofObservables ω ((ω.centered a : 𝒜) * ω.centered a) := by
  rw [← (isSelfAdjoint_centered_mul_self ω a).coe_realPart, ofObservables_apply]
  rfl

/-- Variance is nonnegative. -/
lemma variance_nonneg [StarOrderedRing 𝒜] (ω : 𝓢[ℝ, Observable 𝒜]) (a : Observable 𝒜) :
    0 ≤ ω.variance a := by
  refine ω.map_nonneg ?_
  change (0 : 𝒜) ≤ (ℜ ((ω.centered a : 𝒜) * ω.centered a) : 𝒜)
  rw [(isSelfAdjoint_centered_mul_self ω a).coe_realPart]
  simpa only [(ω.centered a).2.star_eq] using star_mul_self_nonneg (ω.centered a : 𝒜)

end UnitalPositiveLinearMap
