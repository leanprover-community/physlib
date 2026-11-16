/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis

/-!

# Matrices of `PiTensorProduct.map` and dimension of `PiTensorProduct`

This file extends Mathlib's results on the tensor product of two spaces to the tensor product of a
family.

## i. Overview

A tensor with several indices lies in the tensor product `⨂[R] i, M i` of a family of spaces, one
space `M i` for each index `i`. Here `R` is the scalars, `ℝ` or `ℂ` in physics. The results hold for
any commutative semiring, except the dimension (B), which needs a commutative ring. Mathlib proves
several facts about the tensor product of two spaces, `M ⊗ N`, that it does not prove for a family.
This file proves them for a family: the matrix of a map applied at every index (A) and the
dimension (B). It also treats the case with no indices (C).

For example, `T^μ_ν` has `4 · 4 = 16` components, so its space has dimension `16`. A Lorentz
transformation acts on it index by index, by `Λ` at the up index and by `(Λ⁻¹)ᵀ` at the down index.
On the `16` components it is one `16 × 16` matrix, the Kronecker product `Λ ⊗ (Λ⁻¹)ᵀ`, whose entry
at `((μ, ν), (σ, τ))` is `Λ^μ_σ (Λ⁻¹)^τ_ν`. This gives the textbook formula
`T^μ_ν ↦ Λ^μ_σ (Λ⁻¹)^τ_ν T^σ_τ` from the action index by index. A tensor with no indices is a
scalar, which no transformation changes.

## ii. Key results

- `PiTensorProduct.toMatrix_map_apply` : the matrix of `PiTensorProduct.map f` in the product
  bases is the product of the matrices of the `f i`.
- `Module.finrank_piTensorProduct` : the dimension of `⨂[R] i, M i` is `∏ i, finrank R (M i)`.
- `PiTensorProduct.map_eq_id_of_isEmpty` : with no indices, `PiTensorProduct.map f` is the identity.

## iii. Table of contents

- A. Matrices in the product basis
- B. Dimension
- C. Empty index types

## iv. References

* None.

-/

@[expose] public section

open TensorProduct PiTensorProduct

variable {ι R : Type*} {M N : ι → Type*}

/-!

## A. Matrices in the product basis

`PiTensorProduct.map f` applies the map `f i` at every index `i`. It is defined without bases, so
its definition does not give its matrix. In the product bases `Basis.piTensorProduct b`, its matrix
is the Kronecker product of the matrices of the `f i`, whose entry at `(φ, ψ)` is the product over
`i` of the entries of the matrix of `f i` at `(φ i, ψ i)`. So the large matrix on the whole tensor
product is fixed by one small matrix per index. Mathlib proves this for the tensor product of two
spaces, `TensorProduct.toMatrix_map`, and this section proves it for a family.

For example, a Lorentz transformation of `T^μ_ν` is `map` of `Λ` and `(Λ⁻¹)ᵀ`. Its entry at
`((μ, ν), (σ, τ))` is `Λ^μ_σ (Λ⁻¹)^τ_ν`, so the components transform as
`T^μ_ν ↦ Λ^μ_σ (Λ⁻¹)^τ_ν T^σ_τ`.

-/

/-- The matrix of `PiTensorProduct.map f` in the product bases is the n-ary Kronecker product of
the matrices of the `f i`. -/
lemma PiTensorProduct.toMatrix_map_apply [CommSemiring R] [∀ i, AddCommMonoid (M i)]
    [∀ i, Module R (M i)] [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)] [Fintype ι]
    [DecidableEq ι] {κ κ' : ι → Type*} [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
    [∀ i, Fintype (κ' i)]
    (b : Π i, Module.Basis (κ i) R (M i)) (b' : Π i, Module.Basis (κ' i) R (N i))
    (f : Π i, M i →ₗ[R] N i) (φ : Π i, κ' i) (ψ : Π i, κ i) :
    LinearMap.toMatrix (Basis.piTensorProduct b) (Basis.piTensorProduct b')
      (PiTensorProduct.map f) φ ψ = ∏ i, LinearMap.toMatrix (b i) (b' i) (f i) (φ i) (ψ i) := by
  simp [LinearMap.toMatrix_apply, Basis.piTensorProduct_apply,
    Basis.piTensorProduct_repr_tprod_apply]

/-!

## B. Dimension

The dimension of `⨂[R] i, M i` is the product of the dimensions of the `M i`. For example, `T^μ_νρ`
in four dimensions has `4 · 4 · 4 = 64` components. Mathlib proves this for the tensor product of
two spaces, `Module.finrank_tensorProduct`, and this section proves it for a family.

-/

/-- The dimension of `⨂[R] i, M i` is the product of the dimensions of the `M i`. -/
lemma Module.finrank_piTensorProduct [CommRing R] [Fintype ι]
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] [∀ i, Module.Free R (M i)]
    [∀ i, Module.Finite R (M i)] :
    Module.finrank R (⨂[R] i, M i) = ∏ i, Module.finrank R (M i) := by
  classical
  nontriviality R
  rw [Module.finrank_eq_card_basis (Basis.piTensorProduct fun i => Module.Free.chooseBasis R (M i)),
    Fintype.card_pi]
  simp [Module.finrank_eq_card_chooseBasisIndex]

/-!

## C. Empty index types

A tensor with no indices is a scalar. Mathlib identifies `⨂[R] i, M i` over an empty index type
with `R`, by `PiTensorProduct.isEmptyEquiv`. Then a map applied at every index has no index to act
on, so `PiTensorProduct.map f` is the identity (`map_eq_id_of_isEmpty`). For example, a Lorentz
transformation leaves every scalar unchanged.

-/

/-- With no indices, `PiTensorProduct.map f` is the identity. -/
lemma PiTensorProduct.map_eq_id_of_isEmpty [CommSemiring R] [∀ i, AddCommMonoid (M i)]
    [∀ i, Module R (M i)] [IsEmpty ι] (f : Π i, M i →ₗ[R] M i) :
    PiTensorProduct.map f = LinearMap.id := by
  ext x
  simp [Subsingleton.elim (fun i => f i (x i)) x]
