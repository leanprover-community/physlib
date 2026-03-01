/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Algebra.Lie.Classical
import Mathlib.Analysis.Normed.Ring.Lemmas
/-!

# The Minkowski matrix

## i. Overview

The aim of this module is to define the Minkowski matrix `η` in `d+1` dimensions, and
prove properties thereof.

The Minkowski matrix is the real matrix of the form `diag(1, -1, -1, -1, ...)`,
It is related to the Minkowski metric on `ℝ^(d+1)`.

Related to the Minkowski matrix is the notion of the dual of a matrix with respect to
the Minkowski metric. This is defined as `η * Λᵀ * η`, where `Λ` is a real matrix.
This will be used to help define the Lorentz group in later files.

## ii. Key results

- `minkowskiMatrix` : The Minkowski matrix in `d+1` dimensions.
- `minkowskiMatrix.dual` : The dual of a matrix with respect to the Minkowski metric,
  defined to be `η * Λᵀ * η`.

## iii. Table of contents

- A. The Minkowski Matrix
  - A.1. Basic equalities
  - A.2. Notation for the Minkowski matrix
  - A.3. Components of the Minkowski matrix
  - A.4. Squaring the Minkowski matrix
  - A.5. Symmetry properties of the Minkowski matrix
  - A.6. Determinant of the Minkowski matrix
  - A.7. Injective properties of multiplying diagonal components
  - A.8. Action of the Minkowski matrix on vectors
- B. The Minkowski dual
  - B.1. The dual on the identity
  - B.2. The dual swaps multiplication
  - B.3. The dual is an involution
  - B.4. The dual commutes with the transpose
  - B.5. The dual preserves the Minkowski matrix
  - B.6. The dual preserves the determinants
  - B.7. Components of the dual

## iv. References

No references are given here.

-/

open Matrix
/-!

## A. The Minkowski Matrix

We first define the Minkowski matrix in `d+1` dimensions, and prove some basic properties.

-/

/-- The `d.succ`-dimensional real matrix of the form `diag(1, -1, -1, -1, ...)`. -/
def minkowskiMatrix {d : ℕ} : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ :=
  LieAlgebra.Orthogonal.indefiniteDiagonal (Fin 1) (Fin d) ℝ

namespace minkowskiMatrix

variable {d : ℕ}

/-!

### A.1. Basic equalities

We show some basic equalities for the Minkowski matrix.
In particular, we show it can be expressed as a block matrix.

-/
/-- The Minkowski matrix as a diagonal matrix. -/
lemma as_diagonal : @minkowskiMatrix d = diagonal (Sum.elim 1 (-1)) := by
  simp [minkowskiMatrix, LieAlgebra.Orthogonal.indefiniteDiagonal]

/-- The Minkowski matrix as a block matrix. -/
lemma as_block : minkowskiMatrix =
    Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℝ) 0 0 (-1 : Matrix (Fin d) (Fin d) ℝ) := by
  simp [as_diagonal, ← fromBlocks_diagonal, ← diagonal_one]

/-!

### A.2. Notation for the Minkowski matrix

We define the notation `η` for the Minkowski matrix, which can be used when the namespace
`minkowskiMatrix` is opened.

-/

/-- Notation for `minkowskiMatrix`. -/
scoped[minkowskiMatrix] notation "η" => minkowskiMatrix

/-!

### A.3. Components of the Minkowski matrix

We prove some simple properties related to the components of the Minkowski matrix.

-/

/-- The `time-time` component of the Minkowski matrix is `1`. -/
@[simp]
lemma inl_0_inl_0 : @minkowskiMatrix d (Sum.inl 0) (Sum.inl 0) = 1 := by
  rfl

/-- The space diagonal components of the Minkowski matrix are `-1`. -/
@[simp]
lemma inr_i_inr_i (i : Fin d) : @minkowskiMatrix d (Sum.inr i) (Sum.inr i) = -1 := by
  simp [as_diagonal]

/-- The off diagonal elements of the Minkowski matrix are zero. -/
@[simp]
lemma off_diag_zero {μ ν : Fin 1 ⊕ Fin d} (h : μ ≠ ν) : η μ ν = 0 := by
  aesop (add safe forward as_diagonal)

lemma η_diag_ne_zero {μ : Fin 1 ⊕ Fin d} : η μ μ ≠ 0 := by
  aesop (add safe forward as_diagonal)

/-!

### A.4. Squaring the Minkowski matrix

we show that the Minkowski matrix is self-inverting, i.e. `η * η = 1`,
as well as other properties related to squaring the Minkowski matrix.

-/

/-- The Minkowski matrix is self-inverting. -/
@[simp]
lemma sq : @minkowskiMatrix d * minkowskiMatrix = 1 := by
  simp [as_block, fromBlocks_multiply]

/-- Multiplying any element on the diagonal of the Minkowski matrix by itself gives `1`. -/
@[simp]
lemma η_apply_mul_η_apply_diag (μ : Fin 1 ⊕ Fin d) : η μ μ * η μ μ = 1 := by
  aesop (add safe forward as_diagonal)

@[simp]
lemma η_apply_sq_eq_one (μ : Fin 1 ⊕ Fin d) : η μ μ ^ 2 = 1 := by
  cases μ <;> simp [as_diagonal]

/-!

### A.5. Symmetry properties of the Minkowski matrix

The Minkowski matrix is symmetric, due to it being diagonal.

-/

/-- The Minkowski matrix is symmetric. -/
@[simp]
lemma eq_transpose : minkowskiMatrixᵀ = @minkowskiMatrix d := by
  simp [as_diagonal]

/-!

### A.6. Determinant of the Minkowski matrix

We show the determinant of the Minkowski matrix is equal to `(-1)^d` where
`d` is the number of spatial dimensions.

-/

/-- The determinant of the Minkowski matrix is equal to `-1` to the power
  of the number of spatial dimensions. -/
@[simp]
lemma det_eq_neg_one_pow_d : (@minkowskiMatrix d).det = (- 1) ^ d := by
  simp [as_diagonal]

/-!

### A.7. Injective properties of multiplying diagonal components

If `x` and `y` are reals then since `η μ μ` is non-zero for any `μ`, the equation
`η μ μ * x = η μ μ * y` implies `x = y`. We prove this as a lemma.
This is a useful part of the API but is not used often.

-/

lemma mul_η_diag_eq_iff {μ : Fin 1 ⊕ Fin d} {x y : ℝ} :
    η μ μ * x = η μ μ * y ↔ x = y :=
  mul_right_inj' η_diag_ne_zero

/-!

### A.8. Action of the Minkowski matrix on vectors

We show properties of the action of the Minkowski matrix on vectors.

-/

/-- The time components of a vector acted on by the Minkowski matrix remains unchanged. -/
@[simp]
lemma mulVec_inl_0 (v : (Fin 1 ⊕ Fin d) → ℝ) :
    (η *ᵥ v) (Sum.inl 0) = v (Sum.inl 0) := by
  simp [as_diagonal, mulVec_diagonal]

/-- The space components of a vector acted on by the Minkowski matrix swaps sign. -/
@[simp]
lemma mulVec_inr_i (v : (Fin 1 ⊕ Fin d) → ℝ) (i : Fin d) :
    (η *ᵥ v) (Sum.inr i) = - v (Sum.inr i) := by
  simp [as_diagonal, mulVec_diagonal]

/-!

## B. The Minkowski dual

Given a real matrix `Λ`, we define the dual of `Λ` with respect to the Minkowski metric
to be `η * Λᵀ * η`.

The ultimate idea is that for the Minkowski inner product
`⟪Λ x, y⟫ = ⟪x, dual Λ y⟫` for all vectors `x` and `y`.

An element `Λ` is in the Lorentz group if and only if `dual Λ = Λ⁻¹`. This will not be
shown in this module.

This notion of a dual is not quite a homomorphism because it reverses the order of multiplication.
-/

variable (Λ Λ' : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ)

/-- The dual of a matrix with respect to the Minkowski metric.
  A suitable name for this construction is the Minkowski dual. -/
def dual : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ := η * Λᵀ * η

/-!

### B.1. The dual on the identity

We show that the dual of the identity matrix is the identity matrix.

-/

/-- The Minkowski dual of the identity is the identity. -/
@[simp]
lemma dual_id : @dual d 1 = 1 := by
  simpa only [dual, transpose_one, mul_one] using minkowskiMatrix.sq

/-!

### B.2. The dual swaps multiplication

We show that the dual swaps multiplication, i.e. `dual (Λ * Λ') = dual Λ' * dual Λ`.

-/

/-- The Minkowski dual swaps multiplications (acts contravariantly). -/
@[simp]
lemma dual_mul : dual (Λ * Λ') = dual Λ' * dual Λ := by
  simp only [dual, transpose_mul, ← mul_assoc]
  noncomm_ring [minkowskiMatrix.sq]

/-!

### B.3. The dual is an involution

We show that the dual is an involution, i.e. `dual (dual Λ) = Λ`.
-/

/-- The Minkowski dual is involutive (i.e. `dual (dual Λ)) = Λ`). -/
@[simp]
lemma dual_dual : Function.Involutive (@dual d) := by
  intro Λ
  simp only [dual, transpose_mul, eq_transpose, transpose_transpose, ← mul_assoc]
  noncomm_ring [minkowskiMatrix.sq]

/-!

### B.4. The dual commutes with the transpose

-/

/-- The Minkowski dual commutes with the transpose. -/
@[simp]
lemma dual_transpose : dual Λᵀ = (dual Λ)ᵀ := by
  simp [dual, mul_assoc]

/-!

### B.5. The dual preserves the Minkowski matrix

-/

/-- The Minkowski dual preserves the Minkowski matrix. -/
@[simp]
lemma dual_eta : @dual d η = η := by
  simp [dual]

/-!

### B.6. The dual preserves the determinants

-/

/-- The Minkowski dual preserves determinants. -/
@[simp]
lemma det_dual : (dual Λ).det = Λ.det := by
  simp only [dual, det_mul, minkowskiMatrix.det_eq_neg_one_pow_d, det_transpose]
  group
  norm_cast
  simp

/-!

### B.7. Components of the dual

We show a number of properties related to the components of the duals.

-/

/-- Expansion of the components of the Minkowski dual in terms of the components
  of the original matrix. -/
lemma dual_apply (μ ν : Fin 1 ⊕ Fin d) :
    dual Λ μ ν = η μ μ * Λ ν μ * η ν ν := by
  simp [dual, as_diagonal]

/-- The components of the Minkowski dual of a matrix multiplied by the Minkowski matrix
  in terms of the original matrix. -/
lemma dual_apply_minkowskiMatrix (μ ν : Fin 1 ⊕ Fin d) :
    dual Λ μ ν * η ν ν = η μ μ * Λ ν μ := by
  simp [dual_apply, mul_assoc]

end minkowskiMatrix
