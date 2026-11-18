/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.ProbabilisticTheory.State.Basic
public import Physlib.ProbabilisticTheory.Channel.Convex

/-!
# Convex state spaces

Convexity of the state space and its pure and mixed states.

## i. Overview

States mix: a probabilistic combination of two states is again a state, and the state space
embeds convexly into the algebraic dual. A pure state is one that's never a genuine mixture of
two others, an extreme point of that convex set. A mixed state is one that is a mixture.

## ii. Key results

- `ProbabilisticTheory.State.mix` : randomize between two states with a given probability.
- `ProbabilisticTheory.State.stateSpace_convex` : the state space is convex in the algebraic dual.
- `ProbabilisticTheory.State.IsPure` : pure states are extreme points of the state space.
- `ProbabilisticTheory.State.isPure_iff_forall_mix_eq` : a pure state admits only trivial
  genuine mixtures.
- `ProbabilisticTheory.State.isMixed_iff_exists_mem_openSegment` : mixed states lie between
  two other states.

## iii. Table of contents

- A. Mixing states
- B. The state space
- C. Pure and mixed states

## iv. References

-/

@[expose] public section

open ProbabilisticTheory unitInterval

namespace ProbabilisticTheory.State

variable {P : ProbabilisticTheory}

/-!

## A. Mixing states

-/

/-- Randomize between two states with probability `t` of choosing the first, so
`t • ω + σ t • φ` with `σ t = 1 - t`. -/
abbrev mix (ω φ : P.State) (t : unitInterval) : P.State := Channel.mix ω φ t

/-- Evaluation of a mixture is the pointwise convex combination. -/
@[simp]
lemma mix_apply (ω φ : P.State) (t : unitInterval) (A : P.Observables) :
    mix ω φ t A = (t : ℝ) * ω A + (1 - (t : ℝ)) * φ A := rfl

/-- The underlying linear map of a mixture is the corresponding combination of linear maps. -/
lemma toLinearMap_mix (ω φ : P.State) (t : unitInterval) :
    (mix ω φ t).toLinearMap = (t : ℝ) • ω.toLinearMap + (1 - (t : ℝ)) • φ.toLinearMap :=
  Channel.toLinearMap_mix ω φ t

/-- Swapping the two states swaps the weights: `σ` is the symmetry of the interval. -/
lemma mix_symm (ω φ : P.State) (t : unitInterval) : mix ω φ t = mix φ ω (σ t) :=
  Channel.mix_symm ω φ t

/-!

## B. The state space

-/

/-- States embedded into the algebraic dual. -/
abbrev stateSpace : Set (P.Observables →ₗ[ℝ] ℝ) :=
  Channel.channelSpace (P := P) (Q := real)

/-- The state space is convex in the algebraic dual. -/
lemma stateSpace_convex : Convex ℝ (stateSpace (P := P)) :=
  Channel.channelSpace_convex

/-!

## C. Pure and mixed states

-/

/-- A state is pure when it is an extreme point of the state space. -/
def IsPure (ω : P.State) : Prop := ω.toLinearMap ∈ stateSpace.extremePoints ℝ

/-- A state is mixed when it isn't pure. -/
def IsMixed (ω : P.State) : Prop := ¬ ω.IsPure

/-- A state is pure exactly when any open segment containing it has both endpoints equal to it. -/
lemma isPure_iff_forall_mem_openSegment {ω : P.State} :
    ω.IsPure ↔ ∀ φ ψ : P.State,
      ω.toLinearMap ∈ openSegment ℝ φ.toLinearMap ψ.toLinearMap → φ = ω ∧ ψ = ω := by
  simp only [IsPure, mem_extremePoints, stateSpace, Channel.channelSpace,
    Set.forall_mem_range, Function.comp_apply, Channel.toLinearMap_injective.eq_iff]
  exact and_iff_right ⟨ω, rfl⟩

/-- A state is mixed exactly when it lies in an open segment with a different endpoint. -/
lemma isMixed_iff_exists_mem_openSegment {ω : P.State} :
    ω.IsMixed ↔ ∃ φ ψ : P.State,
      ω.toLinearMap ∈ openSegment ℝ φ.toLinearMap ψ.toLinearMap ∧ (φ ≠ ω ∨ ψ ≠ ω) := by
  simp [IsMixed, isPure_iff_forall_mem_openSegment, imp_iff_not_or]

/-- Open segments between states consist exactly of their genuine mixtures. -/
lemma mem_openSegment_iff_exists_mix (ω φ ψ : P.State) :
    ω.toLinearMap ∈ openSegment ℝ φ.toLinearMap ψ.toLinearMap ↔
      ∃ t : unitInterval, 0 < t ∧ t < 1 ∧ mix φ ψ t = ω :=
  Channel.mem_openSegment_iff_exists_mix ω φ ψ

/-- A state is pure exactly when every genuine binary mixture producing it is trivial. -/
lemma isPure_iff_forall_mix_eq {ω : P.State} :
    ω.IsPure ↔ ∀ φ ψ t, 0 < t → t < 1 → mix φ ψ t = ω → φ = ω ∧ ψ = ω := by
  simp only [isPure_iff_forall_mem_openSegment, mem_openSegment_iff_exists_mix,
    forall_exists_index, and_imp]

end ProbabilisticTheory.State
