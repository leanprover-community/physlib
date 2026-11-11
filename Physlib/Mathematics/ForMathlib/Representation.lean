/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Mathlib.RepresentationTheory.Intertwining
public import Physlib.Mathematics.ForMathlib.PiTensorProduct

/-!

# Tensor products of representations and invariant vectors

Tensor products of equivalences of representations, the tensor product of a family of
representations, invariant vectors under an intertwining map, and maps of representations given
by actions.

## i. Overview

An intertwining map `φ` from a representation `ρ` to a representation `σ` satisfies
`φ (ρ g v) = σ g (φ v)`. If `v` is invariant, `ρ g v = v`, then so is `φ v`. Invariance of a tensor
built from an invariant vector by intertwining maps is therefore a corollary, as the invariance of
the Minkowski metric as a tensor follows from the invariance of the bilinear form.

Mathlib has the tensor product of two intertwining maps, `IntertwiningMap.tensor`. Here it is
given for equivalences of representations, `v ⊗ w ↦ φ v ⊗ ψ w`, on the linear equivalence
`TensorProduct.congr`.

A family of representations `ρ i` on `M i` gives the representation `piTprod ρ` on
`⨂[k] i, M i`, `g ↦ ⨂ i, ρ i g`, on Mathlib's `PiTensorProduct.map`. Maps `f i` that intertwine
`ρ i` and `σ i` give `PiTensorProduct.map f`, which intertwines `piTprod ρ` and `piTprod σ`.
Contracting pairs of factors by invariant pairings, `PiTensorProduct.contrPairs`, is also
intertwining.

## ii. Key results

- `Representation.IntertwiningMap.map_invariant` : an intertwining map sends invariant vectors to
  invariant vectors, and `Representation.IntertwiningMap.map_one_invariant` : an intertwining map
  from the trivial representation picks out an invariant vector.
- `Representation.Equiv.tensorCongr` : the tensor product of two equivalences of representations.
- `Representation.piTprod` : the tensor product of a family of representations, with
  `Representation.IsIntertwiningMap.piTensorMap` : `PiTensorProduct.map` of intertwining maps is
  intertwining, `Representation.Equiv.piTensorCongr` : the tensor product of a family of
  equivalences of representations, and `Representation.IsIntertwiningMap.contrPairs` : the
  contraction of invariantly paired factors is intertwining.
- `Representation.IntertwiningMap.map_smul_ofDistribMulAction` and
  `Representation.Equiv.map_smul_ofDistribMulAction` : maps of representations given by actions
  commute with the actions, `φ (g • v) = g • φ v`.

## iii. Table of contents

- A. Invariant vectors
- B. Tensor products of equivalences
- C. Tensor products of families
- D. Representations given by actions

## iv. References

There are no known references for the material in this module.

-/

@[expose] public section

open TensorProduct

variable {k G V W U X : Type*} [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V]
  [AddCommMonoid W] [Module k W] [AddCommMonoid U] [Module k U] [AddCommMonoid X] [Module k X]
  {ρ : Representation k G V} {σ : Representation k G W} {τ : Representation k G U}
  {π : Representation k G X}

/-!

## A. Invariant vectors

-/

/-- An intertwining map sends an invariant vector to an invariant vector,
`ρ g v = v → σ g (φ v) = φ v`. -/
lemma Representation.IntertwiningMap.map_invariant (φ : ρ.IntertwiningMap σ) {v : V} {g : G}
    (hv : ρ g v = v) : σ g (φ v) = φ v := by
  rw [← Representation.IntertwiningMap.isIntertwining, hv]

/-- An intertwining map `φ` from the trivial representation picks out an invariant vector, its
value `φ 1`, as an invariant form picks out its tensor. -/
lemma Representation.IntertwiningMap.map_one_invariant
    (φ : (Representation.trivial k G k).IntertwiningMap ρ) {v : V} (hv : φ 1 = v) (g : G) :
    ρ g v = v :=
  hv ▸ φ.map_invariant rfl

/-!

## B. Tensor products of equivalences

-/

/-- The tensor product of two equivalences of representations, `v ⊗ w ↦ φ v ⊗ ψ w`, Mathlib's
`TensorProduct.congr` with the actions `ρ ⊗ τ` and `σ ⊗ π`. -/
noncomputable def Representation.Equiv.tensorCongr (φ : ρ.Equiv σ) (ψ : τ.Equiv π) :
    (ρ.tprod τ).Equiv (σ.tprod π) :=
  .mk (TensorProduct.congr φ.toLinearEquiv ψ.toLinearEquiv)
    (φ.toIntertwiningMap.tensor ψ.toIntertwiningMap).isIntertwining'

@[simp]
lemma Representation.Equiv.tensorCongr_tmul (φ : ρ.Equiv σ) (ψ : τ.Equiv π) (v : V) (u : U) :
    φ.tensorCongr ψ (v ⊗ₜ u) = φ v ⊗ₜ ψ u := rfl

/-!

## C. Tensor products of families

-/

section

variable {ι : Type*} {M N : ι → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, Module k (M i)]
  [∀ i, AddCommMonoid (N i)] [∀ i, Module k (N i)]

/-- The tensor product of a family of representations, `g ↦ ⨂ i, ρ i g` on `⨂[k] i, M i`. It is
the n-ary `Representation.tprod`. -/
noncomputable def Representation.piTprod (ρ : Π i, Representation k G (M i)) :
    Representation k G (⨂[k] i, M i) :=
  PiTensorProduct.mapMonoidHom.comp (MonoidHom.pi ρ)

lemma Representation.piTprod_apply (ρ : Π i, Representation k G (M i)) (g : G) :
    Representation.piTprod ρ g = PiTensorProduct.map fun i => ρ i g := rfl

@[simp]
lemma Representation.piTprod_tprod (ρ : Π i, Representation k G (M i)) (g : G) (m : Π i, M i) :
    Representation.piTprod ρ g (⨂ₜ[k] i, m i) = ⨂ₜ[k] i, ρ i g (m i) :=
  PiTensorProduct.map_tprod _ _

/-- `PiTensorProduct.map f` intertwines `piTprod ρ` and `piTprod σ` when every `f i` intertwines
`ρ i` and `σ i`. -/
lemma Representation.IsIntertwiningMap.piTensorMap {ρ : Π i, Representation k G (M i)}
    {σ : Π i, Representation k G (N i)} {f : Π i, M i →ₗ[k] N i}
    (hf : ∀ i, (ρ i).IsIntertwiningMap (σ i) (f i)) :
    (Representation.piTprod ρ).IsIntertwiningMap (Representation.piTprod σ)
      (PiTensorProduct.map f) where
  isIntertwining g v := by
    rw [Representation.piTprod_apply, Representation.piTprod_apply, ← LinearMap.comp_apply,
      ← PiTensorProduct.map_comp, ← LinearMap.comp_apply, ← PiTensorProduct.map_comp]
    exact congr(PiTensorProduct.map $(funext fun i => LinearMap.ext ((hf i).isIntertwining g)) v)

/-- The tensor product of a family of equivalences of representations, `⨂ i, v i ↦ ⨂ i, φ i (v i)`.
It is Mathlib's `PiTensorProduct.congr` with the actions `piTprod ρ` and `piTprod σ`. -/
noncomputable def Representation.Equiv.piTensorCongr {ρ : Π i, Representation k G (M i)}
    {σ : Π i, Representation k G (N i)} (φ : Π i, (ρ i).Equiv (σ i)) :
    (Representation.piTprod ρ).Equiv (Representation.piTprod σ) :=
  .mk (PiTensorProduct.congr fun i => (φ i).toLinearEquiv) fun g => LinearMap.ext
    ((Representation.IsIntertwiningMap.piTensorMap fun i =>
      ⟨(φ i).toIntertwiningMap.isIntertwining⟩).isIntertwining g)

@[simp]
lemma Representation.Equiv.piTensorCongr_tprod {ρ : Π i, Representation k G (M i)}
    {σ : Π i, Representation k G (N i)} (φ : Π i, (ρ i).Equiv (σ i)) (m : Π i, M i) :
    Representation.Equiv.piTensorCongr φ (⨂ₜ[k] i, m i) = ⨂ₜ[k] i, φ i (m i) :=
  PiTensorProduct.congr_tprod _ _

/-- `PiTensorProduct.contrPairs p` intertwines `piTprod ρ` and `piTprod` of the kept factors when
every pairing `p j` is invariant. -/
lemma Representation.IsIntertwiningMap.contrPairs {κ J : Type*} [Fintype J]
    {M : κ ⊕ (J ⊕ J) → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, Module k (M i)]
    {ρ : Π i, Representation k G (M i)}
    {p : Π j, M (.inr (.inl j)) ⊗[k] M (.inr (.inr j)) →ₗ[k] k}
    (hp : ∀ j g x y, p j (ρ _ g x ⊗ₜ ρ _ g y) = p j (x ⊗ₜ y)) :
    (Representation.piTprod ρ).IsIntertwiningMap (Representation.piTprod fun x => ρ (.inl x))
      (PiTensorProduct.contrPairs p) where
  isIntertwining g v := by
    induction v using PiTensorProduct.induction_on with
    | smul_tprod r f =>
      simp only [map_smul, Representation.piTprod_tprod, PiTensorProduct.contrPairs_tprod, hp,
        smul_comm r]
    | add x y hx hy => simp only [map_add, hx, hy]

end

/-!

## D. Representations given by actions

-/

section

variable [DistribMulAction G V] [SMulCommClass G k V] [DistribMulAction G W] [SMulCommClass G k W]

/-- An intertwining map of representations given by actions commutes with the actions,
`φ (g • v) = g • φ v`. -/
lemma Representation.IntertwiningMap.map_smul_ofDistribMulAction
    (φ : (Representation.ofDistribMulAction k G V).IntertwiningMap
      (Representation.ofDistribMulAction k G W)) (g : G) (v : V) :
    φ (g • v) = g • φ v :=
  Representation.IntertwiningMap.isIntertwining _ _ φ g v

/-- An equivalence of representations given by actions commutes with the actions,
`φ (g • v) = g • φ v`. -/
lemma Representation.Equiv.map_smul_ofDistribMulAction
    (φ : (Representation.ofDistribMulAction k G V).Equiv
      (Representation.ofDistribMulAction k G W)) (g : G) (v : V) :
    φ (g • v) = g • φ v :=
  φ.toIntertwiningMap.map_smul_ofDistribMulAction g v

end
