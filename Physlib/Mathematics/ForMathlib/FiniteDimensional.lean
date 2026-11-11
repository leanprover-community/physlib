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

- `LinearMap.comp_eq_id_of_comp_eq_id_of_finrank_eq` : `g ∘ f = id` gives `f ∘ g = id` between
  spaces of equal finite dimension.
- `LinearMap.comp_apply_eq_smul_of_comp_apply_eq_smul_of_finrank_eq` : the same up to a nonzero
  scalar, `g (f v) = c • v` for all `v` gives `f (g w) = c • w` for all `w`.

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
    (LinearMap.congr_fun hgf) <| (LinearMap.injective_iff_surjective_of_finrank_eq_finrank h).1 <|
      injective_of_comp_eq_id f g hgf

section Field

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  [FiniteDimensional K V] [FiniteDimensional K W]

/-- Between spaces of equal finite dimension, `g (f v) = c • v` for all `v` and `c ≠ 0` give
`f (g w) = c • w` for all `w`. -/
lemma LinearMap.comp_apply_eq_smul_of_comp_apply_eq_smul_of_finrank_eq
    (h : finrank K V = finrank K W) {f : V →ₗ[K] W} {g : W →ₗ[K] V} {c : K} (hc : c ≠ 0)
    (hgf : ∀ v, g (f v) = c • v) (w : W) : f (g w) = c • w := by
  have := LinearMap.congr_fun (LinearMap.comp_eq_id_of_comp_eq_id_of_finrank_eq h
    (f := f) (g := c⁻¹ • g) (LinearMap.ext fun v => by simp [hgf, smul_smul, hc])) w
  rw [← inv_smul_eq_iff₀ hc]
  simpa [eq_comm] using this

end Field
