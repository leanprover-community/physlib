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

This file extends Mathlib's results on the tensor product of two spaces to the tensor product of a
family, and adds the contraction of its factors in pairs.

## i. Overview

A tensor with several indices lies in the tensor product `⨂[R] i, M i` of a family of spaces, one
space `M i` for each index `i`. Here `R` is the scalars, `ℝ` or `ℂ` in physics, and any commutative
semiring in the results below, with a commutative ring for the dimension (B). Mathlib proves several
facts about the tensor product of two spaces, `M ⊗ N`, that it does not prove for a family. This
file proves them for a family: the matrix of a map applied at every index (A), the dimension (B),
and the case with no indices (C). It also defines contraction, which pairs indices and removes them
(D).

For example, `T^μ_ν` has `4 · 4 = 16` components, so its space has dimension `16`. A Lorentz
transformation acts on it index by index, by `Λ` at the up index and by `(Λ⁻¹)ᵀ` at the down index.
On the `16` components it is one `16 × 16` matrix, the Kronecker product `Λ ⊗ (Λ⁻¹)ᵀ`, whose entry
at `((μ, ν), (σ, τ))` is `Λ^μ_σ (Λ⁻¹)^τ_ν`. This gives the textbook formula
`T^μ_ν ↦ Λ^μ_σ (Λ⁻¹)^τ_ν T^σ_τ` from the action index by index. A tensor with no indices is a
scalar, which no transformation changes. The trace `T^μ_μρ` contracts the first two indices and
keeps `ρ`.

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

/-!

## D. Contraction of pairs of factors

Contraction pairs some indices of a tensor, turns each pair into a scalar, and keeps the other
indices. The index type `κ ⊕ (J ⊕ J)` says which indices are paired, with Mathlib's tags `Sum.inl`
and `Sum.inr` for the left and the right side of `⊕`. The indices `inl x`, for `x` in `κ`, are kept.
Each `j` in `J` is a pair, with first index `inr (inl j)` and second index `inr (inr j)`, contracted
by the pairing `p j`. On a pure tensor, `contrPairs p` multiplies the kept vectors by the product of
the pairings (`contrPairs_tprod`). The nesting follows the construction. Mathlib's
`PiTensorProduct.tmulEquivDep` splits a tensor product over `A ⊕ B` into the tensor product over `A`
times the tensor product over `B`. Splitting at the outer `⊕` separates the kept factors from the
paired ones. Splitting at the inner `⊕` separates the first factor of each pair from the second, so
that `p j` can contract them. A tensor whose indices are in another order is first reordered into
this form.

For example, the Ricci tensor `R_μν = R^ρ_μρν` pairs the first and third indices and keeps the
second and fourth, so its indices are reordered first. On a pure tensor it is
`u ⊗ α ⊗ β ⊗ γ ↦ (β_ρ u^ρ) α ⊗ γ`. The Ricci scalar `R = R^μν_μν` has two pairs and no kept index,
so the result is the scalar `(α_μ u^μ) (β_ν v^ν)` on `u ⊗ v ⊗ α ⊗ β`.

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
