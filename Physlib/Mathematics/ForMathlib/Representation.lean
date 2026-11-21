/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.RepresentationTheory.Intertwining

/-!

# Tensor products of representations

This file gives the representation on the tensor product of a family of representations.

## i. Overview

A tensor such as `T^μ_ν` lies in the tensor product `⨂[k] i, M i` of a family of spaces. Each
index `i` transforms by its own representation `ρ i`, as `Λ` at the up index and `(Λ⁻¹)ᵀ` at the
down index. Mathlib has the representation `ρ.tprod τ` for two factors only.

We define the representation of a family (A). `piTprod ρ` acts by `ρ i g` at each index `i`. A map
out of `⨂[k] i, M i` that commutes with `piTprod ρ` on pure tensors commutes with it on all tensors
(`map_piTprod_of_tprod`).

## ii. Key results

- `Representation.piTprod` : the representation on `⨂[k] i, M i` of a family of representations.
- `Representation.map_piTprod_of_tprod` : a map that commutes with `piTprod ρ` on pure tensors
  commutes with it on all tensors.

## iii. Table of contents

- A. The representation on a tensor product of a family

## iv. References

* None.

-/

@[expose] public section

open TensorProduct

variable {k l G U : Type*} [CommSemiring k] [CommSemiring l] [Monoid G] [AddCommMonoid U]
  [Module l U] {τ : Representation l G U}

/-!

## A. The representation on a tensor product of a family

`piTprod ρ` transforms each index by its own representation. For `T^μ_ν` it sends the pure tensor
`u ⊗ α` to `Λu ⊗ (Λ⁻¹)ᵀα` (`piTprod_tprod`).

-/

namespace Representation

variable {ι : Type*} {M : ι → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, Module k (M i)]

/-- The tensor product of a family of representations, `g ↦ ⨂ i, ρ i g` on `⨂[k] i, M i`. It is
the n-ary `Representation.tprod`. -/
noncomputable def piTprod (ρ : Π i, Representation k G (M i)) : Representation k G (⨂[k] i, M i) :=
  PiTensorProduct.mapMonoidHom.comp (MonoidHom.pi ρ)

/-- On a pure tensor, `piTprod ρ g` acts by `ρ i g` on the vector at each index `i`. -/
@[simp]
lemma piTprod_tprod (ρ : Π i, Representation k G (M i)) (g : G) (m : Π i, M i) :
    piTprod ρ g (⨂ₜ[k] i, m i) = ⨂ₜ[k] i, ρ i g (m i) :=
  PiTensorProduct.map_tprod _ _

/-- A semilinear map out of `⨂ i, M i` that commutes with `piTprod ρ g` on pure tensors commutes
with it on all tensors. The ring map `σ : k →+* l` can be complex conjugation. -/
lemma map_piTprod_of_tprod {σ : k →+* l} {ρ : Π i, Representation k G (M i)}
    (f : (⨂[k] i, M i) →ₛₗ[σ] U) (g : G)
    (h : ∀ m : Π i, M i, f (piTprod ρ g (⨂ₜ[k] i, m i)) = τ g (f (⨂ₜ[k] i, m i)))
    (t : ⨂[k] i, M i) : f (piTprod ρ g t) = τ g (f t) := by
  induction t using PiTensorProduct.induction_on with
  | smul_tprod r m => rw [map_smul, map_smulₛₗ, h, map_smulₛₗ, map_smul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

end Representation
