/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.ProbabilisticTheory.State.Basic
public import Physlib.ProbabilisticTheory.OrderUnit.Basic
public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Topology.UnitInterval

/-!
# Convex state spaces

Convexity of the state space and its pure and mixed states.

## i. Overview

States mix: a probabilistic combination of two states is again a state, and the state space
embeds convexly into the algebraic dual. A pure state is one that's never a genuine mixture of
two others, an extreme point of that convex set. A mixed state is one that is a mixture.

## ii. Key results

- `UnitalPositiveLinearMap.mix` : randomize between two states with a given probability.
- `UnitalPositiveLinearMap.stateSpace_convex` : the state space is convex in the algebraic dual.
- `UnitalPositiveLinearMap.IsPure` : pure states are extreme points of the state space.
- `UnitalPositiveLinearMap.isPure_iff_forall_mix_eq` : a pure state admits only trivial
  genuine mixtures.
- `UnitalPositiveLinearMap.isMixed_iff_exists_mem_openSegment` : mixed states lie between
  two other states.

## iii. Table of contents

- A. Mixing states
- B. The state space
- C. Pure and mixed states

## iv. References

-/

@[expose] public section

open ProbabilisticTheory unitInterval

namespace UnitalPositiveLinearMap

variable {E : Type*} [OrderUnitSpace E]

/-!

## A. Mixing states

-/

/-- Randomize between two states with probability `t` of choosing the first, so
`t • ω + σ t • φ` with `σ t = 1 - t`. -/
def mix (ω φ : 𝓢[ℝ, E]) (t : unitInterval) : 𝓢[ℝ, E] :=
  .ofPositiveLinearMap (toNNReal t • ω + toNNReal (σ t) • φ)
    (by simp [NNReal.smul_def])

/-- Evaluation of a mixture is the pointwise convex combination. -/
@[simp]
lemma mix_apply (ω φ : 𝓢[ℝ, E]) (t : unitInterval) (A : E) :
    mix ω φ t A = (t : ℝ) * ω A + (1 - (t : ℝ)) * φ A := by
  simp [mix, NNReal.smul_def]

/-- The underlying linear map of a mixture is the corresponding combination of linear maps. -/
lemma toLinearMap_mix (ω φ : 𝓢[ℝ, E]) (t : unitInterval) :
    (mix ω φ t).toLinearMap = (t : ℝ) • ω.toLinearMap + (1 - (t : ℝ)) • φ.toLinearMap := by
  ext A
  simp

/-- Swapping the two states swaps the weights: `σ` is the symmetry of the interval. -/
lemma mix_symm (ω φ : 𝓢[ℝ, E]) (t : unitInterval) : mix ω φ t = mix φ ω (σ t) := by
  ext A
  simp [mix_apply, add_comm]

/-!

## B. The state space

-/

/-- States embedded into the algebraic dual. -/
def stateSpace : Set (E →ₗ[ℝ] ℝ) :=
  Set.range fun ω : 𝓢[ℝ, E] => ω.toLinearMap

/-- The state space is convex in the algebraic dual. -/
lemma stateSpace_convex : Convex ℝ (stateSpace (E := E)) := by
  rw [convex_iff_segment_subset]
  rintro _ ⟨ω, rfl⟩ _ ⟨φ, rfl⟩ x hx
  obtain ⟨t, ht, rfl⟩ := (by rwa [segment_symm, segment_eq_image] at hx)
  exact ⟨mix ω φ ⟨t, ht⟩, by simpa only [add_comm] using toLinearMap_mix ω φ ⟨t, ht⟩⟩

/-!

## C. Pure and mixed states

-/

/-- A state is pure when it is an extreme point of the state space. -/
def IsPure (ω : 𝓢[ℝ, E]) : Prop := ω.toLinearMap ∈ stateSpace.extremePoints ℝ

/-- A state is mixed when it isn't pure. -/
def IsMixed (ω : 𝓢[ℝ, E]) : Prop := ¬ ω.IsPure

/-- A state is pure exactly when any open segment containing it has both endpoints equal to it. -/
lemma isPure_iff_forall_mem_openSegment {ω : 𝓢[ℝ, E]} :
    ω.IsPure ↔ ∀ φ ψ : 𝓢[ℝ, E],
      ω.toLinearMap ∈ openSegment ℝ φ.toLinearMap ψ.toLinearMap → φ = ω ∧ ψ = ω := by
  simp only [IsPure, mem_extremePoints, stateSpace, Set.forall_mem_range,
    toLinearMap_injective.eq_iff, Set.mem_range_self, true_and]

/-- A state is mixed exactly when it lies in an open segment with a different endpoint. -/
lemma isMixed_iff_exists_mem_openSegment {ω : 𝓢[ℝ, E]} :
    ω.IsMixed ↔ ∃ φ ψ : 𝓢[ℝ, E],
      ω.toLinearMap ∈ openSegment ℝ φ.toLinearMap ψ.toLinearMap ∧ (φ ≠ ω ∨ ψ ≠ ω) := by
  simp [IsMixed, isPure_iff_forall_mem_openSegment, imp_iff_not_or]

/-- Open segments between states consist exactly of their genuine mixtures. -/
lemma mem_openSegment_iff_exists_mix (ω φ ψ : 𝓢[ℝ, E]) :
    ω.toLinearMap ∈ openSegment ℝ φ.toLinearMap ψ.toLinearMap ↔
      ∃ t : unitInterval, 0 < t ∧ t < 1 ∧ mix φ ψ t = ω := by
  rw [openSegment_symm, openSegment_eq_image]
  simp only [Set.mem_image, Set.mem_Ioo, Subtype.exists,
    ← toLinearMap_injective.eq_iff, toLinearMap_mix, add_comm]
  aesop (add safe forward le_of_lt)

/-- A state is pure exactly when every genuine binary mixture producing it is trivial. -/
lemma isPure_iff_forall_mix_eq {ω : 𝓢[ℝ, E]} :
    ω.IsPure ↔ ∀ φ ψ t, 0 < t → t < 1 → mix φ ψ t = ω → φ = ω ∧ ψ = ω := by
  simp only [isPure_iff_forall_mem_openSegment, mem_openSegment_iff_exists_mix,
    forall_exists_index, and_imp]

end UnitalPositiveLinearMap
