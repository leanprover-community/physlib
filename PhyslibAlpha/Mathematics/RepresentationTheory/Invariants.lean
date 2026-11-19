/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.RepresentationTheory.Invariants
public import PhyslibAlpha.Mathematics.RepresentationTheory.Reynolds.Basic
/-!
# Invariants and intertwining maps out of the trivial representation

How the invariants of a representation control the intertwining maps out of the trivial one.

## i. Overview

The classifications of invariants are stated in one form, `σ.invariants = k ∙ v`,
`σ.invariants = Submodule.span k s` or `σ.invariants = ⊥`. This file turns that form into the
others.

An intertwining map `φ` from the trivial representation on `k` into `σ` is fixed by its value
`φ 1`, which is an invariant of `σ` (A). So once the invariants of `σ` are known to be a line
`k ∙ φ₀ 1`, every such `φ` is a multiple of `φ₀`, and once they are known to be zero, so is every
such `φ`. Likewise every invariant element is a multiple of `v`, or zero (B).

The invariants in the range of an intertwining map `f` out of `σ`, `ρ.invariants ⊓ f.range`,
generalise the invariants of `σ`, which they are for `f` the identity. When every invariant in the
range of `f` is the image of an invariant of `σ`, a descent property, they are the image of the
invariants of `σ`, so a line or zero along with them (C). A Reynolds element of `σ` gives this
property, through `Representation.IsReynolds.exists_mem_invariants_map_eq`. A bijective
intertwining map has it too, and carries the invariants onto the invariants.

## ii. Key results

- `Representation.IntertwiningMap.apply_one_mem_invariants` : the value at `1` of an intertwining
  map out of the trivial representation is invariant.
- `Representation.IntertwiningMap.exists_eq_smul_of_invariants_eq_span` : when the invariants are
  a line, the intertwining maps out of the trivial representation are the multiples of one map.
- `Representation.IntertwiningMap.eq_zero_of_invariants_eq_bot` : when there are no invariants,
  there are no such maps but zero.
- `Representation.exists_eq_smul_of_invariants_eq_span`,
  `Representation.eq_zero_of_invariants_eq_bot` : the invariant elements, from the invariants.
- `Representation.invariants_inf_range_eq_map_of_descent` : with descent, the invariants in the
  range are the image of the invariants.
- `Representation.invariants_inf_range_eq_span_of_descent`,
  `Representation.invariants_inf_range_eq_bot_of_descent` : the line or zero in the range.
- `Representation.IsReynolds.invariants_inf_range_eq_map` : descent from a Reynolds element.
- `Representation.invariants_eq_map_of_bijective` : a bijective intertwining map carries the
  invariants onto the invariants.

## iii. Table of contents

- A. Intertwining maps out of the trivial representation
- B. From the invariants to invariant maps and elements
- C. Invariants in the range of an intertwining map

## iv. References

* None.

-/

@[expose] public section

namespace Representation

variable {k G V W U : Type*} [CommRing k] [Group G] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W] [AddCommGroup U] [Module k U]
  {σ : Representation k G V} {ρ : Representation k G W}

/-!

## A. Intertwining maps out of the trivial representation

-/

namespace IntertwiningMap

/-- An intertwining map sends invariants to invariants. -/
lemma apply_mem_invariants (f : σ.IntertwiningMap ρ) {v : V} (hv : v ∈ σ.invariants) :
    f v ∈ ρ.invariants := fun g => by rw [← f.isIntertwining, hv g]

/-- The value at `1` of an intertwining map out of the trivial representation is invariant. -/
lemma apply_one_mem_invariants (φ : (trivial k G k).IntertwiningMap σ) : φ 1 ∈ σ.invariants :=
  fun g => by simpa using (φ.isIntertwining _ _ g 1).symm

/-- An intertwining map out of the trivial representation is fixed by its value at `1`. -/
lemma ext_one {φ ψ : (trivial k G k).IntertwiningMap σ} (h : φ 1 = ψ 1) : φ = ψ :=
  IntertwiningMap.ext (LinearMap.ext_ring h)

/-!

## B. From the invariants to invariant maps and elements

-/

/-- When the invariants of `σ` are the line through `φ₀ 1`, every intertwining map out of the
  trivial representation is a multiple of `φ₀`. -/
lemma exists_eq_smul_of_invariants_eq_span {φ₀ : (trivial k G k).IntertwiningMap σ}
    (h : σ.invariants = k ∙ φ₀ 1) (φ : (trivial k G k).IntertwiningMap σ) :
    ∃ z : k, φ = z • φ₀ := by
  have hφ := φ.apply_one_mem_invariants
  rw [h, Submodule.mem_span_singleton] at hφ
  obtain ⟨z, hz⟩ := hφ
  exact ⟨z, ext_one (by rw [smul_apply, hz])⟩

/-- When `σ` has no invariants but zero, the only intertwining map out of the trivial
  representation is zero. -/
lemma eq_zero_of_invariants_eq_bot (h : σ.invariants = ⊥)
    (φ : (trivial k G k).IntertwiningMap σ) : φ = 0 := by
  have hφ := φ.apply_one_mem_invariants
  rw [h, Submodule.mem_bot] at hφ
  exact ext_one (by rw [hφ]; rfl)

end IntertwiningMap

/-- The invariants are the line through an invariant `v` when every invariant is a multiple of
  it. -/
lemma invariants_eq_span_singleton {v : V} (hv : v ∈ σ.invariants)
    (h : ∀ x ∈ σ.invariants, ∃ a : k, x = a • v) : σ.invariants = k ∙ v := by
  refine le_antisymm (fun x hx => ?_) ((Submodule.span_singleton_le_iff_mem _ _).2 hv)
  obtain ⟨a, rfl⟩ := h x hx
  exact Submodule.smul_mem _ a (Submodule.mem_span_singleton_self v)

/-- There are no invariants but zero when every invariant vanishes. -/
lemma invariants_eq_bot_of_forall (h : ∀ x ∈ σ.invariants, x = 0) : σ.invariants = ⊥ :=
  eq_bot_iff.2 fun x hx => (Submodule.mem_bot k).2 (h x hx)

/-- When the invariants of `σ` are the line through `v`, every invariant is a multiple of `v`. -/
lemma exists_eq_smul_of_invariants_eq_span {v : V} (h : σ.invariants = k ∙ v) {x : V}
    (hx : ∀ g, σ g x = x) : ∃ a : k, x = a • v := by
  have hx' : x ∈ k ∙ v := h ▸ hx
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hx'
  exact ⟨a, rfl⟩

/-- When `σ` has no invariants but zero, every invariant is zero. -/
lemma eq_zero_of_invariants_eq_bot (h : σ.invariants = ⊥) {x : V} (hx : ∀ g, σ g x = x) :
    x = 0 :=
  (Submodule.mem_bot k).1 (h ▸ hx)

/-!

## C. Invariants in the range of an intertwining map

-/

/-- The invariants in the range of `f` are the image of the invariants of `σ` when every
  invariant in the range is the image of an invariant, the descent property `hd`. -/
lemma invariants_inf_range_eq_map_of_descent (f : σ.IntertwiningMap ρ)
    (hd : ∀ v, f v ∈ ρ.invariants → ∃ w ∈ σ.invariants, f w = f v) :
    ρ.invariants ⊓ f.range.toSubmodule = σ.invariants.map f.toLinearMap := by
  refine le_antisymm (fun b hb => ?_) ?_
  · obtain ⟨v, rfl⟩ := hb.2
    exact hd v hb.1
  · rintro _ ⟨w, hw, rfl⟩
    exact ⟨f.apply_mem_invariants hw, w, rfl⟩

/-- With descent, the invariants in the range of `f` are the line through `f v` when the
  invariants of `σ` are the line through `v`. -/
lemma invariants_inf_range_eq_span_of_descent {v : V} (h : σ.invariants = k ∙ v)
    (f : σ.IntertwiningMap ρ) (hd : ∀ v, f v ∈ ρ.invariants → ∃ w ∈ σ.invariants, f w = f v) :
    ρ.invariants ⊓ f.range.toSubmodule = k ∙ f v := by
  rw [invariants_inf_range_eq_map_of_descent f hd, h, Submodule.map_span, Set.image_singleton]
  rfl

/-- With descent, the invariants in the range of `f` are zero when those of `σ` are. -/
lemma invariants_inf_range_eq_bot_of_descent (h : σ.invariants = ⊥) (f : σ.IntertwiningMap ρ)
    (hd : ∀ v, f v ∈ ρ.invariants → ∃ w ∈ σ.invariants, f w = f v) :
    ρ.invariants ⊓ f.range.toSubmodule = ⊥ := by
  rw [invariants_inf_range_eq_map_of_descent f hd, h, Submodule.map_bot]

/-- A Reynolds element of `σ` on all of `V` gives descent along every intertwining map, so the
  invariants in the range of `f` are the image of the invariants of `σ`. -/
lemma IsReynolds.invariants_inf_range_eq_map {r : MonoidAlgebra k G} (hr : σ.IsReynolds ⊤ r)
    (f : σ.IntertwiningMap ρ) :
    ρ.invariants ⊓ f.range.toSubmodule = σ.invariants.map f.toLinearMap :=
  invariants_inf_range_eq_map_of_descent f fun _ hv => by
    obtain ⟨w, hw, hfw⟩ := hr.exists_mem_invariants_map_eq (f := f.toLinearMap)
      (fun g v => f.isIntertwining _ _ g v) Submodule.mem_top hv
    exact ⟨w, hw.2, hfw⟩

/-- A bijective intertwining map carries the invariants onto the invariants. -/
lemma invariants_eq_map_of_bijective (f : σ.IntertwiningMap ρ) (hf : Function.Bijective f) :
    ρ.invariants = σ.invariants.map f.toLinearMap := by
  refine le_antisymm (fun b hb => ?_) ?_
  · obtain ⟨v, rfl⟩ := hf.2 b
    exact ⟨v, fun g => hf.1 ((f.isIntertwining _ _ g v).trans (hb g)), rfl⟩
  · rintro _ ⟨w, hw, rfl⟩
    exact f.apply_mem_invariants hw

end Representation
