/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Mathlib.RepresentationTheory.Intertwining

/-!

# Equivalences of representations and invariant vectors

The tensor product of two equivalences of representations, and invariant vectors under an
intertwining map.

## i. Overview

An intertwining map `φ` from a representation `ρ` to a representation `σ` satisfies
`φ (ρ g v) = σ g (φ v)`. If `v` is invariant, `ρ g v = v`, then so is `φ v`. Invariance of a tensor
built from an invariant vector by intertwining maps is therefore a corollary, as the invariance of
the Minkowski metric as a tensor follows from the invariance of the bilinear form.

Mathlib has the tensor product of two intertwining maps, `IntertwiningMap.tensor`. Here it is
given for equivalences of representations, `v ⊗ w ↦ φ v ⊗ ψ w`, on the linear equivalence
`TensorProduct.congr`.

## ii. Key results

- `Representation.IntertwiningMap.map_invariant` : an intertwining map sends invariant vectors to
  invariant vectors, and `Representation.IntertwiningMap.map_one_invariant` : an intertwining map
  from the trivial representation picks out an invariant vector.
- `Representation.Equiv.tensorCongr` : the tensor product of two equivalences of representations.

## iii. Table of contents

- A. Invariant vectors
- B. Tensor products of equivalences

## iv. References

-/

@[expose] public section

open TensorProduct

variable {k G V W U X : Type} [CommRing k] [Monoid G] [AddCommMonoid V] [Module k V]
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
