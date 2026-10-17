/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.JordanOrderUnit.Observable

/-!

# Covariance

Covariance of observables in a Jordan order-unit space, and positivity of covariance matrices.

## i. Overview

The Jordan product gives second moments `ω(a ∘ b)` of a state, and so the covariance `Cov_ω(a, b) =
ω(a ∘ b) - ω(a) ω(b)`, with the variance on the diagonal. For a C⋆-algebra this is the symmetrized
quantum covariance `½ ⟨A B + B A⟩ - ⟨A⟩ ⟨B⟩`. Since squares are nonnegative, every covariance matrix
is positive semidefinite, which gives a Cauchy–Schwarz inequality for covariances.

## ii. Key results

- `IsJordanOrderUnit.variance_eq_covarianceForm_self` : the variance is the covariance on the
  diagonal.
- `IsJordanOrderUnit.covarianceForm_isPosSemidef` : the covariance form is positive semidefinite.
- `IsJordanOrderUnit.covariance_cauchy_schwarz` : `Cov(a, b)² ≤ Var(a) Var(b)`.
- `IsJordanOrderUnit.covMatrix_posSemidef` : covariance matrices are positive semidefinite.

## iii. Table of contents

- A. Covariance
- B. Positivity of the covariance matrix

## iv. References

* None.

-/

@[expose] public section

namespace ProbabilisticTheory

namespace IsJordanOrderUnit

variable {E : Type*} [IsJordanOrderUnit E]

/-! ## A. Covariance -/

/-- The Jordan variance is the diagonal of the canonical generic covariance form. -/
lemma variance_eq_covarianceForm_self (ω : 𝓢[ℝ, E]) (a : E) :
    variance ω a = LinearMap.covarianceForm ω.toLinearMap a a := rfl

/-- The state's value on the Jordan product of two centered observables is exactly their
covariance: the algebraic identity underlying `covMatrix_posSemidef` below. -/
lemma moment_centered_mul (ω : 𝓢[ℝ, E]) (a b : E) :
    ω (LinearMap.centered ω.toLinearMap a * LinearMap.centered ω.toLinearMap b) =
      LinearMap.covarianceForm ω.toLinearMap a b := by
  exact LinearMap.apply_centered_mul_centered ω.toLinearMap (map_one ω)
    _root_.one_mul _root_.mul_one a b

/-- The covariance form of a state is positive semidefinite. This is the coordinate-free form of
covariance-matrix positivity and uses only positivity of Jordan squares. -/
lemma covarianceForm_isPosSemidef (ω : 𝓢[ℝ, E]) :
    (LinearMap.covarianceForm ω.toLinearMap).IsPosSemidef where
  isSymm := LinearMap.covarianceForm_isSymm ω.toLinearMap fun a b => mul_comm a b
  isNonneg := ⟨fun a => by
    rw [← moment_centered_mul]
    exact ω.map_nonneg (sq_nonneg (LinearMap.centered ω.toLinearMap a))⟩

/-- **Cauchy–Schwarz for covariances**: `Cov(a, b)² ≤ Var(a) Var(b)`. -/
lemma covariance_cauchy_schwarz (ω : 𝓢[ℝ, E]) (a b : E) :
    (LinearMap.covarianceForm ω.toLinearMap a b) ^ 2 ≤ variance ω a * variance ω b := by
  have h := (LinearMap.covarianceForm ω.toLinearMap).apply_sq_le_of_symm
    (covarianceForm_isPosSemidef ω).isNonneg.nonneg
    (LinearMap.BilinForm.isSymm_iff.mp (covarianceForm_isPosSemidef ω).isSymm) a b
  simpa only [← variance_eq_covarianceForm_self] using h

/-! ## B. Positivity of the covariance matrix -/

/-- **Uncertainty theory, the Jordan-algebraic core**: the covariance matrix of a finite family of
observables is positive semidefinite. This is the coordinate form of
`covarianceForm_isPosSemidef`, obtained by evaluating the form on `∑ i, c i • a i`. -/
lemma covMatrix_posSemidef {ι : Type*} [Fintype ι] (ω : 𝓢[ℝ, E]) (a : ι → E) (c : ι → ℝ) :
    0 ≤ ∑ i, ∑ j, c i * c j * LinearMap.covarianceForm ω.toLinearMap (a i) (a j) := by
  have hnonneg := (covarianceForm_isPosSemidef ω).isNonneg.nonneg (∑ i, c i • a i)
  simp only [map_sum, map_smul, LinearMap.coe_sum, Finset.sum_apply,
    LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum, LinearMap.covarianceForm_apply]
    at hnonneg
  refine hnonneg.trans_eq ?_
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [LinearMap.covarianceForm_isSymm ω.toLinearMap (fun x y => mul_comm x y) |>.eq]
  rw [LinearMap.covarianceForm_apply]
  ring

end IsJordanOrderUnit

end ProbabilisticTheory
