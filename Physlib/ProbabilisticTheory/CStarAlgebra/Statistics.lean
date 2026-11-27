/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.ProbabilisticTheory.CStarAlgebra.Moment

/-!
# Statistics of states

The covariance and the variance of observables in a state of a C⋆-algebra.

## i. Overview

The covariance of two observables `a` and `b` in a state `ω` is the real part of
`ω ((a - ω a) (b - ω b))`. For a family of observables the covariances form the covariance matrix,
which is positive semidefinite. The variance of an observable is its second central moment.

## ii. Key results

- `ProbabilisticTheory.State.covariance` : the covariance of two observables.
- `ProbabilisticTheory.State.posSemidef_covarianceMatrix` : the covariance matrix of a family of
  observables is positive semidefinite.
- `ProbabilisticTheory.State.variance` : the variance of an observable.
- `ProbabilisticTheory.State.variance_nonneg` : the variance is nonnegative.
- `ProbabilisticTheory.State.variance_eq_sub` : the variance is the second moment minus the square
  of the first moment.

## iii. Table of contents

- A. Covariance and variance
- B. Symmetry and positivity of covariance
- C. Properties of variance

## iv. References

* None.

-/

@[expose] public section

open scoped ComplexOrder

namespace ProbabilisticTheory.State

variable {𝒜 : Type*} [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]

/-! ## A. Covariance and variance -/

/-- The covariance of two observables in the state `ω`. -/
noncomputable def covariance (ω : (ofCStarAlgebra 𝒜).State) (a b : selfAdjoint 𝒜) : ℝ :=
  (ω.extend ((ω.centered a : 𝒜) * ω.centered b)).re

/-- The covariance matrix of a family of observables. -/
noncomputable def covarianceMatrix (ω : (ofCStarAlgebra 𝒜).State) {ι : Type*}
    (a : ι → selfAdjoint 𝒜) : Matrix ι ι ℝ :=
  Matrix.of fun i j ↦ ω.covariance (a i) (a j)

/-- The variance of an observable, its second central moment. -/
noncomputable def variance (ω : (ofCStarAlgebra 𝒜).State) (a : selfAdjoint 𝒜) : ℝ :=
  ω.centralMoment a 2

/-! ## B. Symmetry and positivity of covariance -/

/-- Swapping two centered observables conjugates the value of `ω` on their product. -/
lemma extend_centered_mul_swap (ω : (ofCStarAlgebra 𝒜).State) (a b : selfAdjoint 𝒜) :
    ω.extend ((ω.centered b : 𝒜) * ω.centered a) =
      star (ω.extend ((ω.centered a : 𝒜) * ω.centered b)) := by
  rw [← map_star, star_mul, (ω.centered a).2.star_eq, (ω.centered b).2.star_eq]

/-- The covariance is symmetric. -/
lemma covariance_comm (ω : (ofCStarAlgebra 𝒜).State) (a b : selfAdjoint 𝒜) :
    ω.covariance a b = ω.covariance b a := by
  rw [covariance, covariance, extend_centered_mul_swap, Complex.star_def, Complex.conj_re]

/-- In a state, the matrix of expectations of products of centered observables is positive
semidefinite. -/
lemma posSemidef_extend_centered_mul (ω : (ofCStarAlgebra 𝒜).State) {ι : Type*}
    (a : ι → selfAdjoint 𝒜) :
    (Matrix.of fun i j ↦ ω.extend ((ω.centered (a i) : 𝒜) * ω.centered (a j))).PosSemidef := by
  refine ⟨?_, ?_⟩
  · ext i j
    exact (ω.extend_centered_mul_swap (a j) (a i)).symm
  intro c
  convert ω.extend.map_nonneg
    (star_mul_self_nonneg (Finsupp.linearCombination ℂ (Subtype.val ∘ ω.centered ∘ a) c)) using 1
  simp [Finsupp.linearCombination_apply, Finsupp.sum, star_sum, Finset.sum_mul, Finset.mul_sum,
    mul_comm, mul_left_comm, (ω.centered _).2.star_eq]
  exact Finset.sum_comm

/-- The covariance matrix of a family of observables is positive semidefinite. -/
lemma posSemidef_covarianceMatrix (ω : (ofCStarAlgebra 𝒜).State) {ι : Type*}
    (a : ι → selfAdjoint 𝒜) : (ω.covarianceMatrix a).PosSemidef := by
  refine ⟨?_, ?_⟩
  · ext i j
    exact (star_trivial _).trans (covariance_comm ω _ _)
  intro x
  have h := (ω.posSemidef_extend_centered_mul a).2 (x.mapRange Complex.ofReal Complex.ofReal_zero)
  simpa [Finsupp.sum, Finsupp.support_mapRange_of_injective _ x Complex.ofReal_injective,
    Complex.re_sum, covarianceMatrix, covariance] using (Complex.nonneg_iff.mp h).1

/-! ## C. Properties of variance -/

/-- The variance is the value of `ω` on the square of the centered observable. -/
lemma coe_variance (ω : (ofCStarAlgebra 𝒜).State) (a : selfAdjoint 𝒜) :
    (ω.variance a : ℂ) = ω.extend ((ω.centered a : 𝒜) * ω.centered a) := by
  rw [variance, centralMoment, coe_moment, pow_two]

/-- The variance is the covariance of an observable with itself. -/
lemma variance_eq_covariance (ω : (ofCStarAlgebra 𝒜).State) (a : selfAdjoint 𝒜) :
    ω.variance a = ω.covariance a a := by
  rw [covariance, ← coe_variance, Complex.ofReal_re]

/-- The variance is nonnegative. -/
lemma variance_nonneg (ω : (ofCStarAlgebra 𝒜).State) (a : selfAdjoint 𝒜) : 0 ≤ ω.variance a :=
  variance_eq_covariance ω a ▸ (posSemidef_covarianceMatrix ω id).diag_nonneg (i := a)

/-- The variance is the second moment minus the square of the first moment. -/
lemma variance_eq_sub (ω : (ofCStarAlgebra 𝒜).State) (a : selfAdjoint 𝒜) :
    ω.variance a = ω.moment a 2 - ω.moment a 1 ^ 2 := by
  apply Complex.ofReal_injective
  rw [coe_variance, coe_centered, Complex.ofReal_sub, coe_moment, moment_one, pow_two]
  simp [sub_mul, mul_sub, extend_apply]
  ring

end ProbabilisticTheory.State
