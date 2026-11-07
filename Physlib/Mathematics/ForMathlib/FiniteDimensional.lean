/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!

# Left and right inverses between spaces of equal dimension

A left inverse of a linear map between spaces of equal finite dimension is a right inverse.

## i. Overview

Mathlib proves `LinearMap.comp_eq_id_comm` for maps from a space to itself. Here the two maps go
between two spaces `V` and `W` of the same finite dimension: `g ∘ f = id` on `V` gives
`f ∘ g = id` on `W`. The map `f` is injective, so it is bijective, and `g` is its inverse.

## ii. Key results

- `LinearMap.comp_eq_id_comm_of_finrank_eq` : `f ∘ g = id ↔ g ∘ f = id` between spaces of equal
  finite dimension.

## iii. Table of contents

- A. Left and right inverses

## iv. References

-/

@[expose] public section

open Module

variable {K V W : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] [AddCommGroup W]
  [Module K W] [FiniteDimensional K V] [FiniteDimensional K W]

/-!

## A. Left and right inverses

-/

/-- Between spaces of equal finite dimension, a left inverse is a right inverse. -/
lemma LinearMap.comp_eq_id_of_comp_eq_id_of_finrank_eq (h : finrank K V = finrank K W)
    {f : V →ₗ[K] W} {g : W →ₗ[K] V} (hgf : g ∘ₗ f = LinearMap.id) : f ∘ₗ g = LinearMap.id :=
  LinearMap.ext <| Function.LeftInverse.rightInverse_of_surjective (f := g)
    (LinearMap.congr_fun hgf) <|
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank h).1 <| injective_of_comp_eq_id f g hgf

/-- `LinearMap.comp_eq_id_comm` between two spaces of equal finite dimension. -/
lemma LinearMap.comp_eq_id_comm_of_finrank_eq (h : finrank K V = finrank K W) {f : V →ₗ[K] W}
    {g : W →ₗ[K] V} : f ∘ₗ g = LinearMap.id ↔ g ∘ₗ f = LinearMap.id :=
  ⟨LinearMap.comp_eq_id_of_comp_eq_id_of_finrank_eq h.symm,
    LinearMap.comp_eq_id_of_comp_eq_id_of_finrank_eq h⟩
