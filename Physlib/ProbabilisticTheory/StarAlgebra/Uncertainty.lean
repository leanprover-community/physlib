/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Physlib.ProbabilisticTheory.StarAlgebra.Commutator
public import Physlib.ProbabilisticTheory.StarAlgebra.Statistics

/-!
# Uncertainty relations

The commutator of two observables constrains their variances in a state.

## i. Overview

The Robertson relation bounds the product of two variances from below. The bound is the square of
the mean commutator. A state with a nonzero mean commutator thus forbids two small variances.

The Robertson–Schrödinger relation adds the covariance to this bound. The product of two centered
observables has a complex mean. Its real part is the covariance. Its imaginary part is the mean of
the commutator. The relation follows from the Cauchy–Schwarz inequality for the positive form
`(x, y) ↦ ω (x⋆ y)` of the state.

Finitely many observables give a single matrix inequality. The matrix of complex means of products
of centered observables is positive semidefinite. Its real part is the covariance matrix. Its
imaginary part holds the mean commutators. The Robertson–Schrödinger relation is the two variable
case.

## ii. Key results

- `UnitalPositiveLinearMap.ofObservables_centered_mul_centered` : the complex mean of a product of
  centered observables is the covariance plus `i` times the mean commutator.
- `UnitalPositiveLinearMap.robertson_schrodinger` : the Robertson–Schrödinger relation.
- `UnitalPositiveLinearMap.robertson` : the Robertson relation.
- `UnitalPositiveLinearMap.covariance_sq_le` : the covariance is bounded by the variances.
- `UnitalPositiveLinearMap.posSemidef_complexCovarianceMatrix` : the complex covariance matrix is
  positive semidefinite.

## iii. Table of contents

- A. Products of centered observables
- B. Uncertainty relations
- C. Multiple observables

## iv. References

* H. P. Robertson, The Uncertainty Principle (1929). [ref: robertson1929uncertainty]
* E. Schrodinger, Zum Heisenbergschen Unscharfeprinzip (1930). [ref: schrodinger1930heisenberg]

-/

@[expose] public section

open scoped ComplexOrder ComplexStarModule ComplexConjugate

namespace UnitalPositiveLinearMap

variable {𝒜 : Type*} [Ring 𝒜] [PartialOrder 𝒜] [StarRing 𝒜] [Algebra ℂ 𝒜] [StarModule ℂ 𝒜]
  [StarOrderedRing 𝒜] [SelfAdjointDecompose 𝒜]

/-! ## A. Products of centered observables -/

omit [SelfAdjointDecompose 𝒜] in
/-- The complex mean of a product of centered observables is the covariance plus `i` times the
mean commutator. -/
lemma ofObservables_centered_mul_centered (ω : 𝓢[ℝ, Observable 𝒜]) (a b : Observable 𝒜) :
    ofObservables ω ((ω.centered a : 𝒜) * ω.centered b) =
      (ω.covariance a b : ℂ) + (ω ⁅a, b⁆ : ℂ) * Complex.I := by
  rw [Observable.mul_eq_realPart_add_I_smul_bracket, map_add, map_smul, ofObservables_apply,
    ofObservables_apply, centered, centered, Observable.bracket_sub_smul_one, smul_eq_mul,
    mul_comm]
  rfl

/-! ## B. Uncertainty relations -/

/-- The Robertson–Schrödinger uncertainty relation
`cov(a, b)² + (ω ⁅a, b⁆)² ≤ Var(a) Var(b)`. -/
theorem robertson_schrodinger (ω : 𝓢[ℝ, Observable 𝒜]) (a b : Observable 𝒜) :
    ω.covariance a b ^ 2 + ω ⁅a, b⁆ ^ 2 ≤ ω.variance a * ω.variance b := by
  have h := PositiveLinearMap.norm_map_star_mul_sq_le (ofObservables ω) (ω.centered a : 𝒜)
    (ω.centered b : 𝒜)
  rw [(ω.centered a).2.star_eq, (ω.centered b).2.star_eq, ofObservables_centered_mul_centered,
    Complex.sq_norm, Complex.normSq_add_mul_I, ← coe_variance, ← coe_variance, Complex.norm_real,
    Complex.norm_real, Real.norm_of_nonneg (ω.variance_nonneg a),
    Real.norm_of_nonneg (ω.variance_nonneg b)] at h
  exact h

/-- The Robertson uncertainty relation `(ω ⁅a, b⁆)² ≤ Var(a) Var(b)`. -/
theorem robertson (ω : 𝓢[ℝ, Observable 𝒜]) (a b : Observable 𝒜) :
    ω ⁅a, b⁆ ^ 2 ≤ ω.variance a * ω.variance b := by
  nlinarith [robertson_schrodinger ω a b, sq_nonneg (ω.covariance a b)]

/-- The squared covariance is bounded by the product of the variances. -/
lemma covariance_sq_le (ω : 𝓢[ℝ, Observable 𝒜]) (a b : Observable 𝒜) :
    ω.covariance a b ^ 2 ≤ ω.variance a * ω.variance b := by
  nlinarith [robertson_schrodinger ω a b, sq_nonneg (ω ⁅a, b⁆)]

/-! ## C. Multiple observables -/

/-- The complex covariance matrix of a family `a` of observables. Its entries are the complex means
of products of centered observables. -/
noncomputable def complexCovarianceMatrix {ι : Type*} (ω : 𝓢[ℝ, Observable 𝒜])
    (a : ι → Observable 𝒜) : Matrix ι ι ℂ :=
  Matrix.of fun i j ↦ ofObservables ω ((ω.centered (a i) : 𝒜) * ω.centered (a j))

omit [SelfAdjointDecompose 𝒜] in
/-- The entries of the complex covariance matrix are the covariance plus `i` times the mean
commutator. -/
lemma complexCovarianceMatrix_apply {ι : Type*} (ω : 𝓢[ℝ, Observable 𝒜]) (a : ι → Observable 𝒜)
    (i j : ι) :
    ω.complexCovarianceMatrix a i j =
      (ω.covariance (a i) (a j) : ℂ) + (ω ⁅a i, a j⁆ : ℂ) * Complex.I :=
  ofObservables_centered_mul_centered ω (a i) (a j)

/-- The complex covariance matrix of finitely many observables is positive semidefinite. -/
lemma posSemidef_complexCovarianceMatrix {ι : Type*} [Finite ι] (ω : 𝓢[ℝ, Observable 𝒜])
    (a : ι → Observable 𝒜) : (ω.complexCovarianceMatrix a).PosSemidef := by
  have h : ω.complexCovarianceMatrix a = Matrix.gram ℂ
      ((ofObservables ω : 𝒜 →ₚ[ℂ] ℂ).toPreGNS ∘ Subtype.val ∘ ω.centered ∘ a) := by
    ext i j
    simp [complexCovarianceMatrix, Matrix.gram_apply, PositiveLinearMap.preGNS_inner_def,
      (ω.centered (a i)).2.star_eq]
  rw [h]
  exact Matrix.posSemidef_gram ℂ _

end UnitalPositiveLinearMap
