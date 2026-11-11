/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Mathlib.Logic.Equiv.Defs

/-!

# Pairs of elements chosen by an equivalence

An equivalence `σ : ι ≃ κ ⊕ (J ⊕ J)` chooses disjoint pairs of elements of `ι`, one for each `j`.

## i. Overview

An equivalence `σ : ι ≃ κ ⊕ (J ⊕ J)` splits `ι` into the elements `σ.symm (inl x)`, one for each
`x : κ`, and the pairs `σ.symm (inr (inl j))` and `σ.symm (inr (inr j))`, one for each `j : J`. A
contraction of tensor indices is chosen this way, as in `T^ρμ_μ`, where `ρ` is left alone and the
two indices named `μ` form a pair.

Two such equivalences `σ` and `τ` may list the same pairs in another order, or with the two
elements of a pair swapped. `Equiv.SamePair σ τ j j'` says that the pair `j` of `σ` and the pair
`j'` of `τ` are the same two elements, in either order. A pair of one is the same pair as at most
one pair of the other. When `σ` and `τ` agree on `κ` and every pair of `σ` is a pair of `τ`, the
matching of pairs is a bijection `J → J'`.

## ii. Key results

- `Equiv.SamePair` : the pair `j` of `σ` and the pair `j'` of `τ` are the same two elements.
- `Equiv.SamePair.left_unique` and `Equiv.SamePair.right_unique` : the matching of pairs is
  injective in each argument.
- `Equiv.SamePair.bijective` : when `σ` and `τ` agree on `κ`, a matching of every pair of `σ` with
  a pair of `τ` is a bijection.

## iii. Table of contents

- A. The same pair of two equivalences

## iv. References

There are no known references for the material in this module.

-/

@[expose] public section

/-!

## A. The same pair of two equivalences

-/

namespace Equiv

variable {ι κ J J' : Type*}

/-- The pair `j` of `σ` and the pair `j'` of `τ` are the same two elements, in either order. -/
def SamePair (σ : ι ≃ κ ⊕ (J ⊕ J)) (τ : ι ≃ κ ⊕ (J' ⊕ J')) (j : J) (j' : J') : Prop :=
  (σ.symm (.inr (.inl j)) = τ.symm (.inr (.inl j')) ∧
      σ.symm (.inr (.inr j)) = τ.symm (.inr (.inr j'))) ∨
    (σ.symm (.inr (.inl j)) = τ.symm (.inr (.inr j')) ∧
      σ.symm (.inr (.inr j)) = τ.symm (.inr (.inl j')))

instance [DecidableEq ι] (σ : ι ≃ κ ⊕ (J ⊕ J)) (τ : ι ≃ κ ⊕ (J' ⊕ J')) (j : J) (j' : J') :
    Decidable (σ.SamePair τ j j') := by
  unfold SamePair
  infer_instance

variable {σ : ι ≃ κ ⊕ (J ⊕ J)} {τ : ι ≃ κ ⊕ (J' ⊕ J')}

/-- A pair of `τ` is the same pair as at most one pair of `σ`. -/
lemma SamePair.left_unique {j₁ j₂ : J} {j' : J'} (h₁ : σ.SamePair τ j₁ j')
    (h₂ : σ.SamePair τ j₂ j') : j₁ = j₂ := by
  have hσ := σ.symm.injective
  rcases h₁ with ⟨h₁, h₁'⟩ | ⟨h₁, h₁'⟩ <;> rcases h₂ with ⟨h₂, h₂'⟩ | ⟨h₂, h₂'⟩
  · simpa using hσ (h₁.trans h₂.symm)
  · simpa using hσ (h₁'.trans h₂.symm)
  · simpa using hσ (h₁.trans h₂'.symm)
  · simpa using hσ (h₁.trans h₂.symm)

/-- A pair of `σ` is the same pair as at most one pair of `τ`. -/
lemma SamePair.right_unique {j : J} {j₁ j₂ : J'} (h₁ : σ.SamePair τ j j₁)
    (h₂ : σ.SamePair τ j j₂) : j₁ = j₂ := by
  have hτ := τ.symm.injective
  rcases h₁ with ⟨h₁, -⟩ | ⟨h₁, -⟩ <;> rcases h₂ with ⟨h₂, -⟩ | ⟨h₂, -⟩ <;>
    simpa using hτ (h₁.symm.trans h₂)

/-- When `σ` and `τ` agree on `κ` and every pair of `σ` is a pair of `τ`, every pair of `τ` is a
pair of `σ`. -/
lemma exists_samePair_left (hfree : ∀ x, σ.symm (.inl x) = τ.symm (.inl x))
    (h₁ : ∀ j, ∃ j', σ.SamePair τ j j') (j' : J') : ∃ j, σ.SamePair τ j j' := by
  have hτ := τ.symm.injective
  -- The elements of the pair `j'` of `τ` are not in `κ`, so they lie in a pair of `σ`.
  rcases hs : σ (τ.symm (.inr (.inl j'))) with x | j | j <;>
    rw [← Equiv.eq_symm_apply] at hs
  · rw [hfree] at hs
    have := hτ hs
    simp at this
  · obtain ⟨j'', h | h⟩ := h₁ j
    · obtain rfl : j'' = j' := by simpa using hτ (h.1.symm.trans hs.symm)
      exact ⟨j, .inl h⟩
    · have := hτ (h.1.symm.trans hs.symm)
      simp at this
  · obtain ⟨j'', h | h⟩ := h₁ j
    · have := hτ (h.2.symm.trans hs.symm)
      simp at this
    · obtain rfl : j'' = j' := by simpa using hτ (h.2.symm.trans hs.symm)
      exact ⟨j, .inr h⟩

/-- When `σ` and `τ` agree on `κ`, a matching `g` of every pair of `σ` with the same pair of `τ` is
a bijection. -/
lemma SamePair.bijective (hfree : ∀ x, σ.symm (.inl x) = τ.symm (.inl x)) {g : J → J'}
    (hg : ∀ j, σ.SamePair τ j (g j)) : Function.Bijective g :=
  ⟨fun j₁ j₂ hj => (hg j₁).left_unique (hj ▸ hg j₂),
    fun j' => (exists_samePair_left hfree (fun j => ⟨g j, hg j⟩) j').imp
      fun j hj => (hg j).right_unique hj⟩

end Equiv
