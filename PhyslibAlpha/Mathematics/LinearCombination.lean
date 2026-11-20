/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
/-!
# Finite linear combinations under a linear map

## i. Overview

A family `T : ι → B` of vectors of an `R`-module spans Mathlib's
`Submodule.span R (Set.range T)`. The index type is arbitrary and may be empty. When it is
finite, the elements of the span are exactly the combinations `∑ i, c i • T i`, for
coefficients `c : ι → R` that need not be unique (`Submodule.mem_span_range_iff_exists_fun`).
A linear map carries this span to the span of the images of the family
(`Submodule.map_span_range`) (A).

Spans are bounded through their members: the range of a linear map is the span of the images
of a basis, and a product of submodules lying in spans of families lies in any submodule
containing the products of their members (B).

## ii. Key results

- `Submodule.map_span_range` : the image of the span of a family is the span of the images
- `LinearMap.range_eq_span_range_basis` : the range of a linear map is the span of the images of
  a basis
- `Submodule.mul_le_of_le_span_range` : a product of submodules inside spans of families

## iii. Table of contents

- A. The image of the span of a family
- B. Spans bounded through their members

## iv. References

* None.

-/

@[expose] public section

/-!

## A. The image of the span of a family

-/

/-- The image of the span of a family is the span of the images. -/
lemma Submodule.map_span_range {R B B' : Type*} [Semiring R] [AddCommMonoid B] [Module R B]
    [AddCommMonoid B'] [Module R B'] {ι : Sort*} (f : B →ₗ[R] B') (T : ι → B) :
    (Submodule.span R (Set.range T)).map f = Submodule.span R (Set.range fun i => f (T i)) := by
  rw [Submodule.map_span, Set.range_comp']

/-!

## B. Spans bounded through their members

-/

/-- The range of a linear map is the span of the images of a basis. -/
lemma LinearMap.range_eq_span_range_basis {ι R M N : Type*} [Semiring R] [AddCommMonoid M]
    [Module R M] [AddCommMonoid N] [Module R N] (b : Module.Basis ι R M) (f : M →ₗ[R] N) :
    LinearMap.range f = Submodule.span R (Set.range fun i => f (b i)) := by
  rw [LinearMap.range_eq_map, ← b.span_eq, Submodule.map_span_range]

/-- A product of two submodules, each inside the span of a family, lies in any submodule
  containing the products of the members of the two families. -/
lemma Submodule.mul_le_of_le_span_range {ι κ R A : Type*} [CommSemiring R] [Semiring A]
    [Algebra R A] {V V' X : Submodule R A} {a : ι → A} {b : κ → A}
    (hV : V ≤ Submodule.span R (Set.range a)) (hV' : V' ≤ Submodule.span R (Set.range b))
    (hX : ∀ i j, a i * b j ∈ X) : V * V' ≤ X := by
  refine (mul_le_mul' hV hV').trans ?_
  rw [Submodule.span_mul_span, Submodule.span_le]
  rintro _ ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩
  exact hX i j

/-- The three-factor form of `Submodule.mul_le_of_le_span_range`. -/
lemma Submodule.mul_mul_le_of_le_span_range {ι κ ν R A : Type*} [CommSemiring R] [Semiring A]
    [Algebra R A] {V V' V'' X : Submodule R A} {a : ι → A} {b : κ → A} {c : ν → A}
    (hV : V ≤ Submodule.span R (Set.range a)) (hV' : V' ≤ Submodule.span R (Set.range b))
    (hV'' : V'' ≤ Submodule.span R (Set.range c)) (hX : ∀ i j k, a i * (b j * c k) ∈ X) :
    V * (V' * V'') ≤ X :=
  mul_le_of_le_span_range hV
    (mul_le_of_le_span_range (X := Submodule.span R (Set.range fun p : κ × ν => b p.1 * c p.2))
      hV' hV'' fun j k => Submodule.subset_span ⟨(j, k), rfl⟩)
    fun i p => hX i p.1 p.2
