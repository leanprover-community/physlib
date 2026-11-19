/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.RepresentationTheory.Invariants
/-!
# Invariants and intertwining maps out of the trivial representation

How the invariants of a representation control the intertwining maps out of the trivial one.

## i. Overview

An intertwining map `φ` from the trivial representation on `k` into `σ` is fixed by its value
`φ 1`, which is an invariant of `σ` (A). So once the invariants of `σ` are known to be a line
`k ∙ φ₀ 1`, every such `φ` is a multiple of `φ₀`, and once they are known to be zero, so is every
such `φ` (B).

The invariants in the range of an intertwining map `f` out of `σ`, `ρ.invariants ⊓ f.range`,
generalise the invariants of `σ`: for `f` the identity they are the invariants of `σ` itself, and
an intertwining map that is onto `σ` does not change them (C).

## ii. Key results

- `Representation.IntertwiningMap.apply_one_mem_invariants` : the value at `1` of an intertwining
  map out of the trivial representation is invariant.
- `Representation.IntertwiningMap.exists_eq_smul_of_invariants_eq_span` : when the invariants are
  a line, the intertwining maps out of the trivial representation are the multiples of one map.
- `Representation.IntertwiningMap.eq_zero_of_invariants_eq_bot` : when there are no invariants,
  there are no such maps but zero.
- `Representation.invariants_inf_range_eq_span` : the invariants in the range are a line once each
  is a multiple of one of them.
- `Representation.invariants_inf_range_id` : the invariants in the range of the identity are the
  invariants.

## iii. Table of contents

- A. Intertwining maps out of the trivial representation
- B. Classifying those maps by the invariants
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

## B. Classifying those maps by the invariants

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

/-!

## C. Invariants in the range of an intertwining map

-/

/-- The invariants in the range of the identity are the invariants. -/
lemma invariants_inf_range_id :
    σ.invariants ⊓ (IntertwiningMap.id σ).range.toSubmodule = σ.invariants := by
  rw [IntertwiningMap.range_toSubmodule, IntertwiningMap.toLinearMap_id, LinearMap.range_id,
    inf_top_eq]

/-- For an invariant `v`, the invariants in the range of `f` are the line through `f v` as soon
  as each of them is a multiple of `f v`. -/
lemma invariants_inf_range_eq_span {f : σ.IntertwiningMap ρ} {v : V} (hv : v ∈ σ.invariants)
    (h : ∀ b ∈ ρ.invariants, b ∈ f.range.toSubmodule → ∃ z : k, b = z • f v) :
    ρ.invariants ⊓ f.range.toSubmodule = k ∙ f v := by
  refine le_antisymm (fun b hb => ?_) ?_
  · obtain ⟨z, rfl⟩ := h b hb.1 hb.2
    exact Submodule.smul_mem _ z (Submodule.mem_span_singleton_self _)
  · rw [Submodule.span_singleton_le_iff_mem]
    exact ⟨f.apply_mem_invariants hv, v, rfl⟩

/-- The invariants in the range of `f` are zero as soon as each of them is. -/
lemma invariants_inf_range_eq_bot {f : σ.IntertwiningMap ρ}
    (h : ∀ b ∈ ρ.invariants, b ∈ f.range.toSubmodule → b = 0) :
    ρ.invariants ⊓ f.range.toSubmodule = ⊥ :=
  eq_bot_iff.2 fun b hb => (Submodule.mem_bot k).2 (h b hb.1 hb.2)

/-- Precomposing with an intertwining map onto `σ` does not change the invariants in the
  range. -/
lemma invariants_inf_range_comp_of_surjective {τ : Representation k G U}
    (f : σ.IntertwiningMap ρ) (q : τ.IntertwiningMap σ) (hq : Function.Surjective q) :
    ρ.invariants ⊓ (f.comp q).range.toSubmodule = ρ.invariants ⊓ f.range.toSubmodule := by
  rw [IntertwiningMap.range_toSubmodule, IntertwiningMap.range_toSubmodule,
    IntertwiningMap.comp_toLinearMap, LinearMap.range_comp_of_range_eq_top]
  exact LinearMap.range_eq_top.2 hq

end Representation
