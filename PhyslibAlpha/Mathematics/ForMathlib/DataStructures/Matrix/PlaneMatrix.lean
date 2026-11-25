/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Analysis.Complex.Basic
/-!
# Matrices acting in a coordinate plane

The matrices which act on the plane spanned by two coordinates and fix every other coordinate.

## i. Overview

For two coordinates `p` and `q` of `Fin N`, the plane they span is included in `ℂ^N` by the
`N × 2` matrix `planeInclusion p q`, whose columns are the two basis vectors. A `2 × 2` matrix `U`
then acts on the plane and trivially on the other coordinates by the matrix
`planeMatrix p q U = 1 + P (U - 1) Pᵀ`, with `P` the inclusion. These matrices multiply, conjugate
and take determinants as the `2 × 2` matrices do (A), and conjugating a matrix supported on the
plane, or restricting a conjugated matrix to the plane, is computed on the plane (B).

These are the matrix facts behind embedding `SU(2)` in `SU(N)` one coordinate plane at a time.

## ii. Key results

- `Matrix.planeInclusion` : the inclusion of the plane of two coordinates.
- `Matrix.planeMatrix` : the matrix acting as a given `2 × 2` matrix on the plane and trivially
  elsewhere.
- `Matrix.planeMatrix_mul` : plane matrices multiply as the matrices on the plane.
- `Matrix.det_planeMatrix` : a plane matrix has the determinant of the matrix on the plane.
- `Matrix.planeMatrix_conj` : conjugation by a plane matrix of a matrix supported on the plane.

## iii. Table of contents

- A. The plane matrices
- B. Conjugation, blocks and diagonal matrices

## iv. References

* None.

-/

@[expose] public section

namespace Matrix

variable {N : ℕ}

/-!

## A. The plane matrices

-/

/-- The inclusion of the plane of the coordinates `p` and `q`, the `N × 2` matrix whose columns
  are the basis vectors `e_p` and `e_q`. -/
def planeInclusion (p q : Fin N) : Matrix (Fin N) (Fin 2) ℂ :=
  Matrix.of fun x i => if x = ![p, q] i then 1 else 0

@[simp]
lemma planeInclusion_apply (p q : Fin N) (x : Fin N) (i : Fin 2) :
    planeInclusion p q x i = if x = ![p, q] i then 1 else 0 := rfl

/-- The inclusion of the plane of two distinct coordinates is an isometry. -/
lemma planeInclusion_transpose_mul {p q : Fin N} (hpq : p ≠ q) :
    (planeInclusion p q)ᵀ * planeInclusion p q = 1 := by
  ext i j
  simp only [Matrix.mul_apply, transpose_apply, planeInclusion_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, Matrix.one_apply]
  fin_cases i <;> fin_cases j <;> simp [hpq, Ne.symm hpq]

/-- The inclusion of the plane has real entries, so its conjugate transpose is its transpose. -/
lemma conjTranspose_planeInclusion (p q : Fin N) :
    (planeInclusion p q)ᴴ = (planeInclusion p q)ᵀ := by
  ext i x
  simp only [conjTranspose_apply, transpose_apply, planeInclusion_apply]
  split_ifs <;> simp

/-- The matrix acting as `U` on the plane of the coordinates `p` and `q` and as the identity on
  the other coordinates. -/
def planeMatrix (p q : Fin N) (U : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  1 + planeInclusion p q * (U - 1) * (planeInclusion p q)ᵀ

variable {p q : Fin N}

/-- The plane matrix of the identity is the identity. -/
@[simp]
lemma planeMatrix_one : planeMatrix p q 1 = 1 := by
  simp [planeMatrix]

/-- The plane matrices multiply as the matrices on the plane. -/
lemma planeMatrix_mul (hpq : p ≠ q) (U V : Matrix (Fin 2) (Fin 2) ℂ) :
    planeMatrix p q U * planeMatrix p q V = planeMatrix p q (U * V) := by
  set P := planeInclusion p q
  have h : P * (U - 1) * Pᵀ * (P * (V - 1) * Pᵀ) = P * ((U - 1) * (V - 1)) * Pᵀ := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Pᵀ, ← Matrix.mul_assoc Pᵀ,
      planeInclusion_transpose_mul hpq, Matrix.one_mul, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, Matrix.mul_assoc P]
  rw [planeMatrix, planeMatrix, planeMatrix, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add,
    Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, h,
    show U * V - 1 = (U - 1) + (V - 1) + (U - 1) * (V - 1) by noncomm_ring,
    Matrix.mul_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul]
  abel

/-- The conjugate transpose of a plane matrix is the plane matrix of the conjugate
  transpose. -/
lemma conjTranspose_planeMatrix (U : Matrix (Fin 2) (Fin 2) ℂ) :
    (planeMatrix p q U)ᴴ = planeMatrix p q Uᴴ := by
  have hP : (planeInclusion p q)ᵀᴴ = planeInclusion p q := by
    ext x i
    simp only [conjTranspose_apply, transpose_apply, planeInclusion_apply]
    split_ifs <;> simp
  rw [planeMatrix, planeMatrix, conjTranspose_add, conjTranspose_one, conjTranspose_mul,
    conjTranspose_mul, hP, conjTranspose_planeInclusion, conjTranspose_sub, conjTranspose_one,
    Matrix.mul_assoc]

/-- A plane matrix has the determinant of the matrix on the plane. -/
lemma det_planeMatrix (hpq : p ≠ q) (U : Matrix (Fin 2) (Fin 2) ℂ) :
    (planeMatrix p q U).det = U.det := by
  rw [planeMatrix, Matrix.mul_assoc, Matrix.det_one_add_mul_comm, Matrix.mul_assoc,
    planeInclusion_transpose_mul hpq, Matrix.mul_one, add_sub_cancel]

/-- A plane matrix moves the plane as the matrix on the plane does. -/
lemma planeMatrix_mul_planeInclusion (hpq : p ≠ q) (U : Matrix (Fin 2) (Fin 2) ℂ) :
    planeMatrix p q U * planeInclusion p q = planeInclusion p q * U := by
  rw [planeMatrix, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc,
    planeInclusion_transpose_mul hpq, Matrix.mul_one, Matrix.mul_sub, Matrix.mul_one]
  abel

/-- The transpose of the inclusion of the plane intertwines a plane matrix with the matrix on
  the plane. -/
lemma transpose_planeInclusion_mul_planeMatrix (hpq : p ≠ q) (U : Matrix (Fin 2) (Fin 2) ℂ) :
    (planeInclusion p q)ᵀ * planeMatrix p q U = U * (planeInclusion p q)ᵀ := by
  rw [planeMatrix, Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    planeInclusion_transpose_mul hpq, Matrix.one_mul, Matrix.sub_mul, Matrix.one_mul]
  abel

/-!

## B. Conjugation, blocks and diagonal matrices

-/

/-- Conjugating a matrix supported on the plane by a plane matrix conjugates it on the plane. -/
lemma planeMatrix_conj (hpq : p ≠ q) (U M : Matrix (Fin 2) (Fin 2) ℂ) :
    planeMatrix p q U * (planeInclusion p q * M * (planeInclusion p q)ᵀ) * (planeMatrix p q U)ᴴ
      = planeInclusion p q * (U * M * Uᴴ) * (planeInclusion p q)ᵀ := by
  rw [conjTranspose_planeMatrix, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    planeMatrix_mul_planeInclusion hpq, Matrix.mul_assoc, Matrix.mul_assoc,
    transpose_planeInclusion_mul_planeMatrix hpq]
  simp only [Matrix.mul_assoc]

/-- The block on the plane of a matrix conjugated by a plane matrix is the conjugate of its
  block. -/
lemma planeBlock_conj (hpq : p ≠ q) (U : Matrix (Fin 2) (Fin 2) ℂ) (C : Matrix (Fin N) (Fin N) ℂ) :
    (planeInclusion p q)ᵀ * (planeMatrix p q U * C * (planeMatrix p q U)ᴴ) * planeInclusion p q
      = U * ((planeInclusion p q)ᵀ * C * planeInclusion p q) * Uᴴ := by
  rw [conjTranspose_planeMatrix]
  simp only [← Matrix.mul_assoc]
  rw [transpose_planeInclusion_mul_planeMatrix hpq, Matrix.mul_assoc _ (planeMatrix p q Uᴴ),
    planeMatrix_mul_planeInclusion hpq]
  simp only [Matrix.mul_assoc]

/-- The entries of the block on the plane are the entries of the matrix at the two
  coordinates. -/
@[simp]
lemma planeBlock_apply (C : Matrix (Fin N) (Fin N) ℂ) (i j : Fin 2) :
    ((planeInclusion p q)ᵀ * C * planeInclusion p q) i j = C (![p, q] i) (![p, q] j) := by
  simp [Matrix.mul_apply, planeInclusion_apply]

/-- A plane matrix of a diagonal matrix is diagonal. -/
lemma planeMatrix_diagonal (hpq : p ≠ q) (a b : ℂ) :
    planeMatrix p q (diagonal ![a, b])
      = diagonal fun x => if x = p then a else if x = q then b else 1 := by
  ext x y
  simp only [planeMatrix, Matrix.add_apply, Matrix.one_apply, Matrix.mul_apply, transpose_apply,
    planeInclusion_apply, Matrix.sub_apply, diagonal_apply, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  by_cases hxp : x = p <;> by_cases hxq : x = q <;> by_cases hyp : y = p <;>
    by_cases hyq : y = q <;> simp_all [Ne.symm hpq, @eq_comm _ p y, @eq_comm _ q y]

/-- A matrix fixed by conjugation by a plane matrix has its block on the plane fixed by
  conjugation by the matrix on the plane. -/
lemma planeBlock_eq_of_conj_eq (hpq : p ≠ q) {U : Matrix (Fin 2) (Fin 2) ℂ}
    {C : Matrix (Fin N) (Fin N) ℂ} (hC : planeMatrix p q U * C * (planeMatrix p q U)ᴴ = C) :
    U * ((planeInclusion p q)ᵀ * C * planeInclusion p q) * Uᴴ
      = (planeInclusion p q)ᵀ * C * planeInclusion p q := by
  rw [← planeBlock_conj hpq, hC]

/-- The inclusion of the plane carries the matrix units of the plane to those of the
  coordinates. -/
lemma planeInclusion_single (p q : Fin N) (i j : Fin 2) :
    planeInclusion p q * single i j (1 : ℂ) * (planeInclusion p q)ᵀ
      = single (![p, q] i) (![p, q] j) 1 := by
  ext x y
  have h : ∀ a b : Fin N, (if x = a then (1 : ℂ) else 0) * (if y = b then 1 else 0)
      = single a b (1 : ℂ) x y := fun a b => by
    by_cases hx : x = a
    · by_cases hy : y = b
      · subst hx hy
        simp
      · simp [hx, hy, Ne.symm hy]
    · simp [hx, Ne.symm hx]
  rw [← h]
  simp only [Matrix.mul_apply, transpose_apply, planeInclusion_apply, single_apply, ite_and,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [Fintype.sum_eq_single j fun k hk => by simp [Ne.symm hk]]
  simp

end Matrix
