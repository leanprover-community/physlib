/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Mathlib.LinearAlgebra.PiTensorProduct.Basis
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Dimension.Free

/-!

# Matrices of `PiTensorProduct.map` and dimension of `PiTensorProduct`

The matrix of a family of linear maps in the product basis of a `PiTensorProduct`, and the
dimension of a `PiTensorProduct`.

## i. Overview

`PiTensorProduct.map f` applies `f i` at every index `i`. In the product bases
`Basis.piTensorProduct b`, its matrix is the n-ary Kronecker product of the matrices of the `f i`:
its entry at `(φ, ψ)` is the product of the entries at `(φ i, ψ i)`. Mathlib has the binary case,
`TensorProduct.toMatrix_map`.

The dimension of `⨂[R] i, M i` is the product of the dimensions of the `M i`, as
`Module.finrank_tensorProduct` for two factors.

## ii. Key results

- `PiTensorProduct.toMatrix_map_apply` : the matrix of `PiTensorProduct.map f` in the product
  bases is the product of the matrices of the `f i`.
- `Module.finrank_piTensorProduct` : the dimension of `⨂[R] i, M i` is `∏ i, finrank R (M i)`.

## iii. Table of contents

- A. Matrices in the product basis
- B. Dimension

## iv. References

There are no known references for the material in this module.

-/

@[expose] public section

open TensorProduct PiTensorProduct

variable {ι R : Type*} {M N : ι → Type*}

/-!

## A. Matrices in the product basis

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

-/

/-- The dimension of `⨂[R] i, M i` is the product of the dimensions of the `M i`. -/
lemma Module.finrank_piTensorProduct [CommRing R] [StrongRankCondition R] [Fintype ι]
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] [∀ i, Module.Free R (M i)]
    [∀ i, Module.Finite R (M i)] :
    Module.finrank R (⨂[R] i, M i) = ∏ i, Module.finrank R (M i) := by
  classical
  rw [Module.finrank_eq_card_basis (Basis.piTensorProduct fun i => Module.Free.chooseBasis R (M i)),
    Fintype.card_pi]
  simp [Module.finrank_eq_card_chooseBasisIndex]
