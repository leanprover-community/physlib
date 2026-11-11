/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.PiTensorProduct.Dual

/-!

# Matrices of `PiTensorProduct.map`, dimension and contraction of `PiTensorProduct`

The matrix of a family of linear maps in the product basis of a `PiTensorProduct`, the dimension
of a `PiTensorProduct`, `PiTensorProduct.map` on an empty index type, and the contraction of pairs
of factors.

## i. Overview

`PiTensorProduct.map f` applies `f i` at every index `i`. In the product bases
`Basis.piTensorProduct b`, its matrix is the n-ary Kronecker product of the matrices of the `f i`:
its entry at `(φ, ψ)` is the product of the entries at `(φ i, ψ i)`. Mathlib has the binary case,
`TensorProduct.toMatrix_map`.

The dimension of `⨂[R] i, M i` is the product of the dimensions of the `M i`, as
`Module.finrank_tensorProduct` for two factors.

With no indices, `⨂[R] i, M i` is `R` and `PiTensorProduct.map f` is the identity.

On the index type `κ ⊕ (J ⊕ J)`, a family of pairings `p j` of the factors at `inr (inl j)` and
`inr (inr j)` contracts `⨂[R] i, M i` to the tensor product of the factors at `inl x`, as a trace
`T^ρμ_μ` pairs an upper and a lower index.

## ii. Key results

- `PiTensorProduct.toMatrix_map_apply` : the matrix of `PiTensorProduct.map f` in the product
  bases is the product of the matrices of the `f i`.
- `Module.finrank_piTensorProduct` : the dimension of `⨂[R] i, M i` is `∏ i, finrank R (M i)`.
- `PiTensorProduct.map_eq_id_of_isEmpty` : with no indices, `PiTensorProduct.map f` is the identity.
- `PiTensorProduct.contrPairs` : the contraction of pairs of factors by a family of pairings, with
  `PiTensorProduct.contrPairs_tprod` : its value on a pure tensor.

## iii. Table of contents

- A. Matrices in the product basis
- B. Dimension
- C. Empty index types
- D. Contraction of pairs of factors

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

/-!

## C. Empty index types

-/

/-- With no indices, `PiTensorProduct.map f` is the identity. -/
lemma PiTensorProduct.map_eq_id_of_isEmpty [CommSemiring R] [∀ i, AddCommMonoid (M i)]
    [∀ i, Module R (M i)] [IsEmpty ι] (f : Π i, M i →ₗ[R] M i) :
    PiTensorProduct.map f = LinearMap.id := by
  ext x
  simp [Subsingleton.elim (fun i => f i (x i)) x]

/-!

## D. Contraction of pairs of factors

-/

section

variable [CommSemiring R] {κ J : Type*} [Fintype J] {M : κ ⊕ (J ⊕ J) → Type*}
  [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

/-- The contraction of `⨂ i, M i` on `κ ⊕ (J ⊕ J)` that pairs the factors at `inr (inl j)` and
`inr (inr j)` by `p j` and keeps the factors at `inl x`. -/
noncomputable def PiTensorProduct.contrPairs
    (p : Π j, M (.inr (.inl j)) ⊗[R] M (.inr (.inr j)) →ₗ[R] R) :
    (⨂[R] i, M i) →ₗ[R] ⨂[R] x, M (.inl x) :=
  -- The factors of each pair are split into two tensor products, and the second is read as a
  -- linear form on the first through the `p j` and Mathlib's `PiTensorProduct.dualDistrib`.
  (TensorProduct.rid R _).toLinearMap ∘ₗ
    (TensorProduct.lift (PiTensorProduct.dualDistrib ∘ₗ
      PiTensorProduct.map fun j => (TensorProduct.curry (p j)).flip).flip ∘ₗ
      (tmulEquivDep R fun i => M (.inr i)).symm.toLinearMap).lTensor _ ∘ₗ
    (tmulEquivDep R M).symm.toLinearMap

/-- On a pure tensor the contraction multiplies the kept factors by the pairings of each pair. -/
lemma PiTensorProduct.contrPairs_tprod
    (p : Π j, M (.inr (.inl j)) ⊗[R] M (.inr (.inr j)) →ₗ[R] R) (f : Π i, M i) :
    contrPairs p (⨂ₜ[R] i, f i) =
      (∏ j, p j (f (.inr (.inl j)) ⊗ₜ f (.inr (.inr j)))) • ⨂ₜ[R] x, f (.inl x) := by
  simp [contrPairs, tmulEquivDep_symm_apply]

end
