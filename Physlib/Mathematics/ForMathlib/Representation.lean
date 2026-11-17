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

This file gives the representation on the tensor product of a family of representations, and makes
Mathlib's linear maps of such products into maps of representations.

## i. Overview

A map of representations from `ρ` on `V` to `σ` on `W` is a linear map `φ : V → W` that commutes
with the group, `φ ∘ ρ g = σ g ∘ φ`. Mathlib calls it an `IntertwiningMap`, and an `Equiv` when it
is invertible. Lowering an index with the metric, `v ↦ η v`, is one from the vectors, with
`ρ g = Λ`, to the covectors, with `σ g = (Λ⁻¹)ᵀ`, since `Λᵀ η Λ = η`.

A tensor such as `T^μ_ν` has one representation `ρ i` for each index `i` and lies in the tensor
product `⨂[k] i, M i` of the family. Mathlib has the representation `ρ.tprod τ` and the map
`IntertwiningMap.tensor` for two factors only. This file gives the representation for a family,
`piTprod ρ` (A), and proves that `PiTensorProduct.map` of maps of representations is one (B).

## ii. Key results

- `Representation.piTprod` : the representation on `⨂[k] i, M i` of a family of representations.
- `Representation.map_piTprod_of_tprod` : a map that commutes with `piTprod ρ` on pure tensors
  commutes with it on all tensors.
- `Representation.IsIntertwiningMap.piTprodMap` : `PiTensorProduct.map` of maps of
  representations.

## iii. Table of contents

- A. The representation on a tensor product of a family
- B. Maps of representations

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

variable {ι : Type*} {M N : ι → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, Module k (M i)]
  [∀ i, AddCommMonoid (N i)] [∀ i, Module k (N i)]

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

/-!

## B. Maps of representations

`piTprodMap` applies a map at every index, such as lowering every index, `T^μν ↦ T_μν`. It commutes
with the group when each of the maps does.

-/

/-- `PiTensorProduct.map f` intertwines `piTprod ρ` and `piTprod σ` when every `f i` intertwines
`ρ i` and `σ i`. -/
lemma IsIntertwiningMap.piTprodMap {ρ : Π i, Representation k G (M i)}
    {σ : Π i, Representation k G (N i)} {f : Π i, M i →ₗ[k] N i}
    (hf : ∀ i, (ρ i).IsIntertwiningMap (σ i) (f i)) :
    (piTprod ρ).IsIntertwiningMap (piTprod σ) (PiTensorProduct.map f) where
  isIntertwining g v := by
    change PiTensorProduct.map f (PiTensorProduct.map (fun i => ρ i g) v) =
      PiTensorProduct.map (fun i => σ i g) (PiTensorProduct.map f v)
    rw [← LinearMap.comp_apply, ← PiTensorProduct.map_comp, ← LinearMap.comp_apply,
      ← PiTensorProduct.map_comp]
    exact congr(PiTensorProduct.map $(funext fun i => LinearMap.ext ((hf i).isIntertwining g)) v)

end Representation
