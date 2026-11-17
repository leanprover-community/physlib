/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.LinearAlgebra.Pi
/-!
# Functoriality of the pointwise lift of linear maps

`LinearMap.piMap` preserves identities and compositions.

## i. Overview

`LinearMap.piMap f` applies a family of linear maps `f i : φ i →ₗ ψ i` slot by slot to
`∀ i, φ i`. It sends the family of identities to the identity and a family of compositions to
the composition of the lifts. These are the two facts used to show that a family of
representations, acting slot by slot, is again a representation.

## ii. Key results

- `LinearMap.piMap_id` : the lift of the identities is the identity.
- `LinearMap.piMap_comp_piMap` : the lift of compositions is the composition of the lifts.

## iii. Table of contents

- A. Identities and compositions

## iv. References

- None.

-/

@[expose] public section

namespace LinearMap

/-!

## A. Identities and compositions

-/

/-- The pointwise lift of the identity maps is the identity. -/
lemma piMap_id {R ι : Type*} {φ : ι → Type*} [Semiring R]
    [∀ i, AddCommMonoid (φ i)] [∀ i, Module R (φ i)] :
    LinearMap.piMap (fun i => (LinearMap.id : φ i →ₗ[R] φ i)) = LinearMap.id :=
  LinearMap.ext fun _ => funext fun _ => rfl

/-- The pointwise lift of compositions is the composition of the pointwise lifts. -/
lemma piMap_comp_piMap {R ι : Type*} {φ ψ ω : ι → Type*} [Semiring R]
    [∀ i, AddCommMonoid (φ i)] [∀ i, Module R (φ i)]
    [∀ i, AddCommMonoid (ψ i)] [∀ i, Module R (ψ i)]
    [∀ i, AddCommMonoid (ω i)] [∀ i, Module R (ω i)]
    (f : ∀ i, ψ i →ₗ[R] ω i) (g : ∀ i, φ i →ₗ[R] ψ i) :
    (LinearMap.piMap f).comp (LinearMap.piMap g)
      = LinearMap.piMap fun i => (f i).comp (g i) :=
  LinearMap.ext fun _ => funext fun _ => rfl

end LinearMap
