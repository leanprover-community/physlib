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
- `Module.Basis.tensorProductToMatrix_map` : the coefficient matrix of `f ⊗ g` applied to `v`.
- `Module.Basis.tensorProductToMatrix_symm_map` : `f ⊗ g` applied to the tensor with coefficient
  matrix `X`.
- `Module.Basis.tensorProduct_repr_comm` : swapping the factors of a tensor transposes its
  coefficients.

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

variable [DecidableEq ι] [DecidableEq κ]

/-- The tensor with coefficient matrix `X` is `∑ i j, X i j • b₁ i ⊗ b₂ j`. -/
lemma tensorProductToMatrix_symm_apply (X : Matrix ι κ R) :
    (b₁.tensorProductToMatrix b₂).symm X = ∑ i, ∑ j, X i j • (b₁ i ⊗ₜ[R] b₂ j) := by
  rw [LinearEquiv.symm_apply_eq]
  ext i j
  simp [Finsupp.single_apply, Finset.sum_apply]

/-- The coefficient matrix of `f ⊗ g v` is `A * X * Bᵀ`, with `X` that of `v` and `A` and `B` the
matrices of `f` and `g`. -/
lemma tensorProductToMatrix_map (f : M →ₗ[R] M) (g : N →ₗ[R] N) (v : M ⊗[R] N) :
    b₁.tensorProductToMatrix b₂ (TensorProduct.map f g v) =
      toMatrix b₁ b₁ f * b₁.tensorProductToMatrix b₂ v * (toMatrix b₂ b₂ g)ᵀ := by
  ext i j
  simp only [tensorProductToMatrix_apply, Matrix.mul_apply, Matrix.transpose_apply]
  rw [← LinearMap.toMatrix_mulVec_repr (b₁.tensorProduct b₂) (b₁.tensorProduct b₂),
    TensorProduct.toMatrix_map]
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, kroneckerMap_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

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

end Module.Basis
