/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Mathlib.RepresentationTheory.Intertwining
public import Physlib.Mathematics.ForMathlib.PiTensorProduct

/-!

# Tensor products of representations

This file gives the representation on the tensor product of a family of representations, and makes
Mathlib's linear maps of such products into maps of representations.

## i. Overview

A representation `ρ` of a group or monoid `G` on a space `V` says how each element `g` of `G` acts
on `V`, by the linear map `ρ g`. A map of representations from `ρ` to `σ` on `W` is a linear map
`φ : V → W` that commutes with the group, `φ ∘ ρ g = σ g ∘ φ` for every `g`, where `∘` applies the
right-hand map first. So transforming and then mapping is the same as mapping and then transforming,
and the square

```
        ρ g
    V ──────► V
    │         │
  φ │         │ φ
    ▼         ▼
    W ──────► W
        σ g
```

commutes. Mathlib calls it an `IntertwiningMap`, and an `Equiv` when it is invertible.

For example, let `G` be the Lorentz group, and let `Λ` be the matrix of a Lorentz transformation
`g`. Then `g` acts on the vectors `V` by `ρ g = Λ`, and on the covectors `W` by `σ g = (Λ⁻¹)ᵀ`, so
that `α_μ v^μ` is invariant. The map `φ` is lowering an index with the metric, `φ v = η v`, from
vectors to covectors. Composing maps is multiplying their matrices, so the two routes in the square
are `φ ∘ ρ g = η Λ` and `σ g ∘ φ = (Λ⁻¹)ᵀ η`. They agree because `Λᵀ η Λ = η`, the defining
property of a Lorentz transformation.

A tensor with several indices has one representation for each index, a family `ρ i` of
representations of `G` on spaces `M i`. For `T^μ_ν` the family is `Λ` on the vectors at the up index
and `(Λ⁻¹)ᵀ` on the covectors at the down index. The tensor lies in the tensor product `⨂[k] i, M i`
of the family. Mathlib has the representation `ρ.tprod τ` on the tensor product of two
representations, and the tensor product `IntertwiningMap.tensor` of two intertwining maps, but no
representation on the tensor product of a family. So Mathlib's `PiTensorProduct.map` is not stated
as a map of representations. This file defines that representation, `piTprod ρ` (A), and proves that
applying maps of representations at the factors commutes with it (B).

## ii. Key results

- `Representation.piTprod` : the representation on `⨂[k] i, M i` of a family of representations.
- `Representation.map_piTprod_of_tprod` : a map that commutes with `piTprod ρ` on pure tensors
  commutes with it on all tensors.
- `Representation.IsIntertwiningMap.piTprodMap` and `Representation.Equiv.piTprodCongr` :
  `PiTensorProduct.map` and `PiTensorProduct.congr` of maps of representations.

## iii. Table of contents

- A. The representation on a tensor product of a family
- B. Maps of representations

## iv. References

* None.

-/

@[expose] public section

open TensorProduct

variable {k G U : Type*} [CommSemiring k] [Monoid G] [AddCommMonoid U] [Module k U]
  {τ : Representation k G U}

/-!

## A. The representation on a tensor product of a family

Given how the group acts at each index, by the family `ρ`, the representation `piTprod ρ` acts on
the whole tensor by transforming every index by its own rule, `g ↦ ⨂ i, ρ i g` on `⨂[k] i, M i`.
For `T^μ_ν`, with `Λ` at the up index and `(Λ⁻¹)ᵀ` at the down index, it is
`T^μ_ν ↦ Λ^μ_σ (Λ⁻¹)^τ_ν T^σ_τ`, and on a pure tensor `u ⊗ α ↦ Λu ⊗ (Λ⁻¹)ᵀ α` (`piTprod_tprod`).
It is Mathlib's `Representation.tprod` on `V ⊗ W` for a family of factors, through
`PiTensorProduct.map`.

A semilinear map out of `⨂ i, M i` that commutes with `piTprod ρ g` on pure tensors `⨂ₜ i, m i`
commutes with it on all tensors (`map_piTprod_of_tprod`), since pure tensors span `⨂ i, M i`.

-/

namespace Representation

variable {ι : Type*} {M N : ι → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, Module k (M i)]
  [∀ i, AddCommMonoid (N i)] [∀ i, Module k (N i)]

/-- The tensor product of a family of representations, `g ↦ ⨂ i, ρ i g` on `⨂[k] i, M i`. It is
the n-ary `Representation.tprod`. -/
noncomputable def piTprod (ρ : Π i, Representation k G (M i)) : Representation k G (⨂[k] i, M i) :=
  PiTensorProduct.mapMonoidHom.comp (MonoidHom.pi ρ)

@[simp]
lemma piTprod_tprod (ρ : Π i, Representation k G (M i)) (g : G) (m : Π i, M i) :
    piTprod ρ g (⨂ₜ[k] i, m i) = ⨂ₜ[k] i, ρ i g (m i) :=
  PiTensorProduct.map_tprod _ _

/-- A semilinear map out of `⨂ i, M i`, such as a conjugate-linear one, that commutes with
`piTprod ρ g` on pure tensors commutes with it on all tensors. -/
lemma map_piTprod_of_tprod {φ : k →+* k} {ρ : Π i, Representation k G (M i)}
    (f : (⨂[k] i, M i) →ₛₗ[φ] U) (g : G)
    (h : ∀ m : Π i, M i, f (piTprod ρ g (⨂ₜ[k] i, m i)) = τ g (f (⨂ₜ[k] i, m i)))
    (t : ⨂[k] i, M i) : f (piTprod ρ g t) = τ g (f t) := by
  induction t using PiTensorProduct.induction_on with
  | smul_tprod r m => rw [map_smul, map_smulₛₗ, h, map_smulₛₗ, map_smul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

/-!

## B. Maps of representations

`piTprodMap` applies a map at every index, such as lowering every index, `T^μν ↦ T_μν`. It commutes
with the group when each of the maps does, and `piTprodCongr` is the same for equivalences of
representations.

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

namespace Equiv

/-- The tensor product of a family of equivalences of representations, `⨂ i, v i ↦ ⨂ i, φ i (v i)`.
It is Mathlib's `PiTensorProduct.congr` with the actions `piTprod ρ` and `piTprod σ`. -/
noncomputable def piTprodCongr {ρ : Π i, Representation k G (M i)}
    {σ : Π i, Representation k G (N i)} (φ : Π i, (ρ i).Equiv (σ i)) :
    (piTprod ρ).Equiv (piTprod σ) :=
  .mk (PiTensorProduct.congr fun i => (φ i).toLinearEquiv) fun g => LinearMap.ext
    ((IsIntertwiningMap.piTprodMap fun i =>
      ⟨(φ i).toIntertwiningMap.isIntertwining⟩).isIntertwining g)

@[simp]
lemma piTprodCongr_tprod {ρ : Π i, Representation k G (M i)}
    {σ : Π i, Representation k G (N i)} (φ : Π i, (ρ i).Equiv (σ i)) (m : Π i, M i) :
    piTprodCongr φ (⨂ₜ[k] i, m i) = ⨂ₜ[k] i, φ i (m i) :=
  PiTensorProduct.congr_tprod _ _

end Equiv

end Representation
