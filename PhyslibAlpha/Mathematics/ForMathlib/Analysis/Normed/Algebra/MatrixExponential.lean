/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.Data.Matrix.Block
public import Mathlib.Analysis.SpecialFunctions.Exponential
/-!
# Exponentials of block-diagonal, Kronecker and scalar matrices

The matrix exponential of a block-diagonal matrix, of a Kronecker sum and of a scalar shift.

## i. Overview

The exponential of complex matrices commutes with the continuous ring homomorphisms built
from block-diagonal matrices and Kronecker products. So `exp (diag(A, B))` is
`diag(exp A, exp B)`, and `exp (A ⊗ 1 + 1 ⊗ B)` is `exp A ⊗ exp B`. The two terms of the
Kronecker sum commute. A scalar shift `A + z 1` multiplies the exponential by `exp z`.

## ii. Key results

- `Matrix.exp_fromBlocks_zero` : `exp (diag(A, B)) = diag(exp A, exp B)`.
- `Matrix.exp_kronecker_one_add_one_kronecker` : `exp (A ⊗ 1 + 1 ⊗ B) = exp A ⊗ exp B`.
- `Matrix.exp_add_smul_one` : `exp (A + z 1) = exp z • exp A`.
- `Matrix.exp_scalar` : the exponential of a scalar matrix.

## iii. Table of contents

- A. Block-diagonal matrices
- B. Kronecker products
- C. Scalar matrices

## iv. References

* None.

-/

@[expose] public section

open NormedSpace Kronecker

namespace Matrix

variable {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-!

## A. Block-diagonal matrices

-/

set_option backward.isDefEq.respectTransparency false in
/-- The exponential of a block-diagonal matrix is block-diagonal,
  `exp (diag(A, B)) = diag(exp A, exp B)`. -/
lemma exp_fromBlocks_zero (A : Matrix m m ℂ) (B : Matrix n n ℂ) :
    exp (fromBlocks A 0 0 B) = fromBlocks (exp A) 0 0 (exp B) := by
  let f : Matrix m m ℂ × Matrix n n ℂ →+* Matrix (m ⊕ n) (m ⊕ n) ℂ :=
    { toFun X := fromBlocks X.1 0 0 X.2
      map_one' := fromBlocks_one
      map_mul' X Y := by simp [fromBlocks_multiply]
      map_zero' := by simp
      map_add' X Y := by simp [fromBlocks_add] }
  have hf : Continuous f :=
    continuous_fst.matrix_fromBlocks continuous_const continuous_const continuous_snd
  open scoped Norms.Operator in
  have h := map_exp f hf (A, B)
  open scoped Norms.Operator in
  rw [show exp (A, B) = (exp A, exp B) from Prod.ext (Prod.fst_exp _) (Prod.snd_exp _)] at h
  exact h.symm

/-!

## B. Kronecker products

-/

set_option backward.isDefEq.respectTransparency false in
/-- The exponential of the Kronecker sum is the Kronecker product of the exponentials,
  `exp (A ⊗ 1 + 1 ⊗ B) = exp A ⊗ exp B`. -/
lemma exp_kronecker_one_add_one_kronecker (A : Matrix m m ℂ) (B : Matrix n n ℂ) :
    exp (A ⊗ₖ (1 : Matrix n n ℂ) + (1 : Matrix m m ℂ) ⊗ₖ B) = exp A ⊗ₖ exp B := by
  have hc : Commute (A ⊗ₖ (1 : Matrix n n ℂ)) ((1 : Matrix m m ℂ) ⊗ₖ B) := by
    rw [Commute, SemiconjBy, ← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.mul_one,
      Matrix.one_mul, Matrix.mul_one, Matrix.one_mul]
  let f : Matrix m m ℂ →+* Matrix (m × n) (m × n) ℂ :=
    { toFun X := X ⊗ₖ (1 : Matrix n n ℂ)
      map_one' := one_kronecker_one
      map_mul' X Y := by rw [← mul_kronecker_mul, Matrix.mul_one]
      map_zero' := zero_kronecker _
      map_add' X Y := add_kronecker _ _ _ }
  let g : Matrix n n ℂ →+* Matrix (m × n) (m × n) ℂ :=
    { toFun X := (1 : Matrix m m ℂ) ⊗ₖ X
      map_one' := one_kronecker_one
      map_mul' X Y := by rw [← mul_kronecker_mul, Matrix.mul_one]
      map_zero' := kronecker_zero _
      map_add' X Y := kronecker_add _ _ _ }
  have hf : Continuous f := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    exact ((continuous_apply _).comp (continuous_apply _)).mul continuous_const
  have hg : Continuous g := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    exact continuous_const.mul ((continuous_apply _).comp (continuous_apply _))
  rw [Matrix.exp_add_of_commute _ _ hc]
  open scoped Norms.Operator in
  rw [show A ⊗ₖ (1 : Matrix n n ℂ) = f A from rfl,
    show (1 : Matrix m m ℂ) ⊗ₖ B = g B from rfl, ← map_exp f hf, ← map_exp g hg]
  show exp A ⊗ₖ 1 * (1 ⊗ₖ exp B) = _
  rw [← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]

/-!

## C. Scalar matrices

-/

set_option backward.isDefEq.respectTransparency false in
/-- Adding a scalar matrix multiplies the exponential by the exponential of the scalar. -/
lemma exp_add_smul_one (A : Matrix m m ℂ) (z : ℂ) :
    exp (A + z • (1 : Matrix m m ℂ)) = Complex.exp z • exp A := by
  rw [Matrix.exp_add_of_commute _ _ ((Commute.one_right A).smul_right z),
    ← Algebra.algebraMap_eq_smul_one]
  open scoped Norms.Operator in
  rw [← algebraMap_exp_comm, Complex.exp_eq_exp_ℂ, Algebra.algebraMap_eq_smul_one,
    Matrix.mul_smul, Matrix.mul_one]

/-- The exponential of a scalar matrix is the scalar matrix of the exponential. -/
lemma exp_scalar (z : ℂ) : exp (scalar m z) = scalar m (Complex.exp z) := by
  rw [scalar_apply, Matrix.exp_diagonal, scalar_apply, Complex.exp_eq_exp_ℂ]
  rw [Pi.exp_def]

end Matrix
