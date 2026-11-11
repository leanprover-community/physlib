/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Matrix

/-!

# Tensor products of linear maps on coefficient matrices

In bases `b₁` and `b₂`, `TensorProduct.map f g` acts on the coefficient matrix of a tensor by
`X ↦ A * X * Bᵀ`, with `A` and `B` the matrices of `f` and `g`.

## i. Overview

A tensor `v` in `M ⊗ N` has the coefficient matrix `X i j = (b₁.tensorProduct b₂).repr v (i, j)`,
and `b₁.tensorProductToMatrix b₂` is the linear equivalence `v ↦ X`. The map `f ⊗ g` sends `X` to
`A * X * Bᵀ`. For a Lorentz tensor `T^μν` and a Lorentz transformation `Λ` this is
`T^μν ↦ Λ^μ_ρ T^ρσ Λ^ν_σ`.

## ii. Key results

- `Module.Basis.tensorProductToMatrix` : the coefficient matrix of a tensor in `M ⊗ N`.
- `Module.Basis.tensorProductToMatrix_symm_apply` : the tensor with coefficient matrix `X` is
  `∑ i j, X i j • b₁ i ⊗ b₂ j`.
- `Module.Basis.tensorProductToMatrix_tmul` : the coefficient matrix of `x ⊗ y` is the outer
  product of the coordinates.
- `Module.Basis.tensorProductToMatrix_symm_diagonal` : the tensor with the diagonal coefficient
  matrix `diagonal D` is `∑ i, D i • b i ⊗ b i`.
- `Module.Basis.tensorProductToMatrix_map` : the coefficient matrix of `f ⊗ g` applied to `v`.
- `Module.Basis.tensorProductToMatrix_symm_map` : `f ⊗ g` applied to the tensor with coefficient
  matrix `X`.
- `Module.Basis.tensorProduct_repr_comm` : swapping the factors of a tensor transposes its
  coefficients.
- `Module.Basis.comm_eq_smul_iff` : swapping the factors scales a tensor of `M ⊗ M` by `r` exactly
  when its coefficient matrix satisfies `Xᵀ = r X`, symmetric for `r = 1` and antisymmetric for
  `r = -1`.

## iii. Table of contents

- A. The action on coefficient matrices
- B. Swapping the factors

## iv. References

There are no known references for the material in this module.

-/

@[expose] public section

/-!

## A. The action on coefficient matrices

-/

namespace Module.Basis

open Matrix LinearMap TensorProduct

section Action

variable {R M N ι κ : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N] [Module R M]
  [Module R N] [Fintype ι] [Fintype κ] (b₁ : Basis ι R M) (b₂ : Basis κ R N)

/-- The coefficient matrix `X i j = (b₁.tensorProduct b₂).repr v (i, j)` of a tensor `v` in
`M ⊗ N`. -/
noncomputable def tensorProductToMatrix : M ⊗[R] N ≃ₗ[R] Matrix ι κ R :=
  (b₁.tensorProduct b₂).repr ≪≫ₗ Finsupp.linearEquivFunOnFinite R R (ι × κ) ≪≫ₗ
    LinearEquiv.curry R R ι κ

@[simp]
lemma tensorProductToMatrix_apply (v : M ⊗[R] N) (i : ι) (j : κ) :
    b₁.tensorProductToMatrix b₂ v i j = (b₁.tensorProduct b₂).repr v (i, j) := rfl

/-- The coefficient matrix of `x ⊗ y` is the outer product of the coordinates of `x` and `y`. -/
lemma tensorProductToMatrix_tmul (x : M) (y : N) :
    b₁.tensorProductToMatrix b₂ (x ⊗ₜ y) = vecMulVec (b₁.repr x) (b₂.repr y) := by
  ext i j
  simp [vecMulVec_apply, mul_comm]

variable [DecidableEq ι] [DecidableEq κ]

/-- The coefficient matrix of `f ⊗ g v` is `A * X * Bᵀ`, with `X` that of `v` and `A` and `B` the
matrices of `f` and `g`. -/
lemma tensorProductToMatrix_map (f : M →ₗ[R] M) (g : N →ₗ[R] N) (v : M ⊗[R] N) :
    b₁.tensorProductToMatrix b₂ (TensorProduct.map f g v) =
      toMatrix b₁ b₁ f * b₁.tensorProductToMatrix b₂ v * (toMatrix b₂ b₂ g)ᵀ := by
  induction v using TensorProduct.inductionOn with
  | tmul x y => simp only [map_tmul, tensorProductToMatrix_tmul, mul_vecMulVec, vecMulVec_mul,
      vecMul_transpose, toMatrix_mulVec_repr]
  | add v w hv hw => simp only [map_add, hv, hw, Matrix.mul_add, Matrix.add_mul]

/-- The tensor with coefficient matrix `X` is `∑ i j, X i j • b₁ i ⊗ b₂ j`. -/
lemma tensorProductToMatrix_symm_apply (X : Matrix ι κ R) :
    (b₁.tensorProductToMatrix b₂).symm X = ∑ i, ∑ j, X i j • (b₁ i ⊗ₜ[R] b₂ j) := by
  rw [LinearEquiv.symm_apply_eq]
  ext i j
  simp [Finsupp.single_apply, Finset.sum_apply]

/-- The tensor with the diagonal coefficient matrix `diagonal D` is `∑ i, D i • b i ⊗ b i`. -/
lemma tensorProductToMatrix_symm_diagonal (D : ι → R) :
    (b₁.tensorProductToMatrix b₁).symm (diagonal D) = ∑ i, D i • (b₁ i ⊗ₜ[R] b₁ i) := by
  simp [tensorProductToMatrix_symm_apply, diagonal_apply, ite_smul]

/-- `f ⊗ g` sends the tensor with coefficient matrix `X` to the one with coefficient matrix
`A * X * Bᵀ`. -/
lemma tensorProductToMatrix_symm_map (f : M →ₗ[R] M) (g : N →ₗ[R] N) (X : Matrix ι κ R) :
    TensorProduct.map f g ((b₁.tensorProductToMatrix b₂).symm X) =
      (b₁.tensorProductToMatrix b₂).symm (toMatrix b₁ b₁ f * X * (toMatrix b₂ b₂ g)ᵀ) := by
  rw [LinearEquiv.eq_symm_apply, tensorProductToMatrix_map, LinearEquiv.apply_symm_apply]

end Action

/-!

## B. Swapping the factors

-/

variable {R M N ι κ : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N] [Module R M]
  [Module R N]

/-- Swapping the factors of `v` transposes its coefficients, as `(Tᵀ)^νμ = T^μν`. -/
lemma tensorProduct_repr_comm (b₁ : Basis ι R M) (b₂ : Basis κ R N) (v : M ⊗[R] N) (i : ι)
    (j : κ) :
    (b₂.tensorProduct b₁).repr (TensorProduct.comm R M N v) (j, i) =
      (b₁.tensorProduct b₂).repr v (i, j) := by
  induction v using TensorProduct.inductionOn with
  | tmul x y => simp [mul_comm]
  | add x y hx hy => simp [hx, hy]

/-- Swapping the factors scales `v` by `r` exactly when its coefficients do, `X j i = r X i j`. -/
lemma comm_eq_smul_iff (b : Basis ι R M) (v : M ⊗[R] M) (r : R) :
    TensorProduct.comm R M M v = r • v ↔
      ∀ i j, (b.tensorProduct b).repr v (j, i) = r * (b.tensorProduct b).repr v (i, j) := by
  rw [← (b.tensorProduct b).repr.injective.eq_iff, Finsupp.ext_iff, Prod.forall]
  simp only [tensorProduct_repr_comm, map_smul, Finsupp.smul_apply, smul_eq_mul]

end Module.Basis
