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

A tensor with several indices lies in the tensor product `⨂[R] i, M i` of a family of spaces.
Mathlib gives the matrix of a map and the dimension only for two spaces, `M ⊗ N`.

We give the matrix of `PiTensorProduct.map` for a family (A). For `T^μ_ν` a Lorentz transformation
acts by the Kronecker product `Λ ⊗ (Λ⁻¹)ᵀ` of its matrices at the two indices. This is the textbook
formula `T^μ_ν ↦ Λ^μ_σ (Λ⁻¹)^τ_ν T^σ_τ`. We then give the dimension (B). `T^μ_ν` has `4 · 4 = 16`
components. Finally we treat the case with no indices (C). The results hold over any commutative
semiring, and the dimension needs the strong rank condition.

## ii. Key results

- `PiTensorProduct.toMatrix_map` : the matrix of `PiTensorProduct.map f` in the product bases is
  the Kronecker product of the matrices of the `f i`, with `PiTensorProduct.toMatrix_map_apply` :
  its entries.
- `Module.finrank_piTensorProduct` : the `finrank` of `⨂[R] i, M i` is `∏ i, finrank R (M i)`.
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

This section extends Mathlib's `TensorProduct.toMatrix_map` from two spaces to a family.

-/

section

variable [CommSemiring R] [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
  [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)] [Fintype ι] [DecidableEq ι]
  {κ κ' : ι → Type*} [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)] [∀ i, Fintype (κ' i)]
  (b : Π i, Module.Basis (κ i) R (M i)) (b' : Π i, Module.Basis (κ' i) R (N i))
  (f : Π i, M i →ₗ[R] N i)

/-- The matrix of `PiTensorProduct.map f` in the product bases is the n-ary Kronecker product of
the matrices of the `f i`. Its entry at `(φ, ψ)` is `∏ i, (f i)_(φ i, ψ i)`. -/
lemma PiTensorProduct.toMatrix_map :
    LinearMap.toMatrix (Basis.piTensorProduct b) (Basis.piTensorProduct b') (map f) =
      Matrix.of fun φ ψ => ∏ i, LinearMap.toMatrix (b i) (b' i) (f i) (φ i) (ψ i) := by
  ext φ ψ
  simp [LinearMap.toMatrix_apply, Basis.piTensorProduct_apply,
    Basis.piTensorProduct_repr_tprod_apply]

/-- The entry of the matrix of `PiTensorProduct.map f` at `(φ, ψ)` is the product of the entries
of the matrices of the `f i` at `(φ i, ψ i)`. -/
lemma PiTensorProduct.toMatrix_map_apply (φ : Π i, κ' i) (ψ : Π i, κ i) :
    LinearMap.toMatrix (Basis.piTensorProduct b) (Basis.piTensorProduct b')
      (PiTensorProduct.map f) φ ψ = ∏ i, LinearMap.toMatrix (b i) (b' i) (f i) (φ i) (ψ i) := by
  rw [toMatrix_map, Matrix.of_apply]

end

/-!

## B. Dimension

This section extends Mathlib's `Module.finrank_tensorProduct` from two spaces to a family.

-/

/-- The `finrank` of `⨂[R] i, M i` is the product of the `finrank` of each `M i`. -/
lemma Module.finrank_piTensorProduct [CommSemiring R] [StrongRankCondition R] [Fintype ι]
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] [∀ i, Module.Free R (M i)] :
    Module.finrank R (⨂[R] i, M i) = ∏ i, Module.finrank R (M i) := by
  classical
  simp_rw [Module.finrank_eq_nat_card_basis
    (Basis.piTensorProduct fun i => Module.Free.chooseBasis R (M i)), Nat.card_pi,
    Module.finrank_eq_nat_card_basis (Module.Free.chooseBasis R _)]

/-!

## C. Empty index types

A tensor with no indices is a scalar. A map at every index is the identity on it, so a Lorentz
transformation leaves every scalar unchanged.

-/

/-- With no indices, `PiTensorProduct.map f` is the identity. -/
lemma PiTensorProduct.map_eq_id_of_isEmpty [CommSemiring R] [∀ i, AddCommMonoid (M i)]
    [∀ i, Module R (M i)] [IsEmpty ι] (f : Π i, M i →ₗ[R] M i) :
    PiTensorProduct.map f = LinearMap.id := by
  rw [Subsingleton.elim f fun _ => LinearMap.id, PiTensorProduct.map_id]
