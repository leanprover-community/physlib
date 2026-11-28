/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Symmetric

/-!

# A left inverse of a symmetric matrix is a right inverse

A square matrix equal to its transpose has every left inverse as a right inverse.

## i. Overview

A two-sided inverse of a matrix is usually certified by both products being the identity. When
the matrix equals its transpose, one product suffices: transposing `ginv * g = 1` gives
`g * ginv = 1` once `g` is replaced by its transpose, and associativity then shows that `ginv`
is its own transpose. No determinant or nonsingularity hypothesis is used.

## ii. Key results

- `mul_eq_one_of_isSymm_of_mul_eq_one` : a left inverse of a symmetric square matrix is a right
  inverse.

## iii. Table of contents

- A. Symmetric left inverses

## iv. References

* None.

-/

@[expose] public section

/-!

## A. Symmetric left inverses

-/

/-- A left inverse of a symmetric square matrix is also a right inverse. -/
lemma mul_eq_one_of_isSymm_of_mul_eq_one {n : ℕ} {g ginv : Matrix (Fin n) (Fin n) ℝ}
    (hsymm : g.IsSymm) (h : ginv * g = 1) : g * ginv = 1 := by
  have htrans : g * Matrix.transpose ginv = 1 := by
    have := congrArg Matrix.transpose h
    rwa [Matrix.transpose_mul, Matrix.transpose_one, hsymm.eq] at this
  have hginv : ginv = Matrix.transpose ginv := by
    calc ginv = ginv * 1 := (Matrix.mul_one ginv).symm
      _ = ginv * (g * Matrix.transpose ginv) := by rw [htrans]
      _ = (ginv * g) * Matrix.transpose ginv := by rw [Matrix.mul_assoc]
      _ = 1 * Matrix.transpose ginv := by rw [h]
      _ = Matrix.transpose ginv := Matrix.one_mul _
  rwa [← hginv] at htrans
