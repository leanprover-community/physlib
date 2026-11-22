/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis

/-!

# Matrices, dimension and empty index types of `PiTensorProduct`

This file extends Mathlib's matrix and dimension results for the tensor product of two modules to
the tensor product of a family.

## i. Overview

A tensor with several indices lies in the tensor product `⨂[R] i, M i` of a family of modules
`M i`. Mathlib gives the matrix of a map and the dimension for two factors, `M ⊗ N`. This file
gives them for a family.

Take a tensor `T^μν` with components in the basis `e_μ ⊗ e_ν`, and linear maps `f₁` and `f₂` with
matrices `(f₁)^μ_σ` and `(f₂)^ν_τ`. The map `PiTensorProduct.map ![f₁, f₂]` applies `f₁` at the
first index and `f₂` at the second, `T^μν ↦ (f₁)^μ_σ (f₂)^ν_τ T^στ`. Its matrix has the entry
`(f₁)^μ_σ (f₂)^ν_τ` at row `(μ, ν)` and column `(σ, τ)`, the Kronecker product of the two matrices
(A). With four values of each index, `T^μν` has `4 · 4 = 16` components, the product of the
dimensions of the factors (B). A tensor with no indices is a scalar, and `PiTensorProduct.map f`
with no indices is the identity (C). The dimension formula holds for free modules over a commutative
semiring `R` with the strong rank condition, as in `Module.finrank_tensorProduct`.

## ii. Key results

- `PiTensorProduct.toMatrix_map` : the matrix of `PiTensorProduct.map f` in the product bases is
  the Kronecker product of the matrices of the `f i`, and `PiTensorProduct.toMatrix_map_apply` :
  its entries.
- `Module.finrank_piTensorProduct` : the `finrank` of `⨂[R] i, M i` is `∏ i, finrank R (M i)`.
- `PiTensorProduct.map_eq_id_of_isEmpty` : with no indices, `PiTensorProduct.map f` is the identity.

## iii. Table of contents

- A. Matrices in the product basis
- B. Dimension
- C. Empty index types

## iv. References

There are no known references for the material in this module.

-/

@[expose] public section

open TensorProduct PiTensorProduct

variable {ι R : Type*} {M N : ι → Type*}

/-!

## A. Matrices in the product basis

This section extends Mathlib's `TensorProduct.toMatrix_map` from two modules to a family.

-/

section

variable [CommSemiring R] [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
  [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)] [Fintype ι] [DecidableEq ι]
  {κ κ' : ι → Type*} [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)] [∀ i, Finite (κ' i)]
  (b : Π i, Module.Basis (κ i) R (M i)) (b' : Π i, Module.Basis (κ' i) R (N i))
  (f : Π i, M i →ₗ[R] N i)

/-- The entry of the matrix of `PiTensorProduct.map f` at `(φ, ψ)` is the product of the entries
of the matrices of the `f i` at `(φ i, ψ i)`. -/
lemma PiTensorProduct.toMatrix_map_apply (φ : Π i, κ' i) (ψ : Π i, κ i) :
    LinearMap.toMatrix (Basis.piTensorProduct b) (Basis.piTensorProduct b')
      (PiTensorProduct.map f) φ ψ = ∏ i, LinearMap.toMatrix (b i) (b' i) (f i) (φ i) (ψ i) := by
  simp [LinearMap.toMatrix_apply]

/-- The matrix of `PiTensorProduct.map f` in the product bases is the Kronecker product of
the matrices of the `f i`. -/
lemma PiTensorProduct.toMatrix_map :
    LinearMap.toMatrix (Basis.piTensorProduct b) (Basis.piTensorProduct b') (map f) =
      Matrix.of fun φ ψ => ∏ i, LinearMap.toMatrix (b i) (b' i) (f i) (φ i) (ψ i) :=
  Matrix.ext (toMatrix_map_apply b b' f)

end

/-!

## B. Dimension

This section extends Mathlib's `Module.finrank_tensorProduct` from two modules to a family.

-/

/-- The `finrank` of `⨂[R] i, M i` is the product of the `finrank` of each `M i`. -/
@[simp]
lemma Module.finrank_piTensorProduct [CommSemiring R] [StrongRankCondition R] [Fintype ι]
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] [∀ i, Module.Free R (M i)] :
    Module.finrank R (⨂[R] i, M i) = ∏ i, Module.finrank R (M i) := by
  simp_rw [Module.finrank_eq_nat_card_basis
    (Basis.piTensorProduct fun i => Module.Free.chooseBasis R (M i)), Nat.card_pi,
    Module.finrank_eq_nat_card_basis (Module.Free.chooseBasis R _)]

/-!

## C. Empty index types

A tensor with no indices is a scalar, and a map at every index leaves it unchanged.

-/

/-- With no indices, `PiTensorProduct.map f` is the identity. -/
lemma PiTensorProduct.map_eq_id_of_isEmpty [CommSemiring R] [∀ i, AddCommMonoid (M i)]
    [∀ i, Module R (M i)] [IsEmpty ι] (f : Π i, M i →ₗ[R] M i) :
    PiTensorProduct.map f = LinearMap.id := by
  rw [Subsingleton.elim f fun _ => LinearMap.id, PiTensorProduct.map_id]
