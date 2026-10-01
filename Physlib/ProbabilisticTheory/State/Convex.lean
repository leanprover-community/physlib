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

## i. Overview

States mix: a probabilistic combination of two states is again a state, and the state space
embeds convexly into the algebraic dual. A pure state is one that's never a genuine mixture of
two others, an extreme point of that convex set. A mixed state is one that is a mixture.

## ii. Key results

- `UnitalPositiveLinearMap.mix` : randomize between two states with a given probability.
- `UnitalPositiveLinearMap.stateSpace_convex` : the state space is convex in the algebraic dual.
- `UnitalPositiveLinearMap.isPure_iff_forall_mix_eq` : a state is pure iff every genuine mixture
  producing it is trivial.

## iii. Table of contents

- A. Mixing states
- B. The state space
- C. Pure and mixed states

-/

@[expose] public section

namespace UnitalPositiveLinearMap

variable {E : Type*} [OrderUnitSpace E]

/-!

## A. Mixing states

-/

/-- Randomize between two states with probability `t` of choosing the first. -/
def mix (ω φ : 𝓢[ℝ, E]) (t : unitInterval) : 𝓢[ℝ, E] :=
  ofLinearMap ((t : ℝ) • ω.toLinearMap + (1 - (t : ℝ)) • φ.toLinearMap)
    (fun _ hA => add_nonneg (mul_nonneg t.2.1 (map_nonneg ω hA))
      (mul_nonneg (sub_nonneg.mpr t.2.2) (map_nonneg φ hA)))
    (show (t : ℝ) * ω 1 + (1 - (t : ℝ)) * φ 1 = 1 by simp)

/-- Evaluation of a mixture is the pointwise convex combination. -/
@[simp]
lemma mix_apply (ω φ : 𝓢[ℝ, E]) (t : unitInterval) (A : E) :
    mix ω φ t A = (t : ℝ) * ω A + (1 - (t : ℝ)) * φ A := rfl

/-!

## B. The state space

-/

/-- States embedded into the algebraic dual. -/
def stateSpace : Set (E →ₗ[ℝ] ℝ) :=
  Set.range fun ω : 𝓢[ℝ, E] => ω.toLinearMap

/-- The state space is convex in the algebraic dual. -/
lemma stateSpace_convex : Convex ℝ (stateSpace (E := E)) := by
  rintro x ⟨ω, rfl⟩ y ⟨φ, rfl⟩ t s ht hs hts
  have hst : s = 1 - t := by linarith
  subst hst
  exact ⟨mix ω φ ⟨t, ht, by linarith⟩, rfl⟩

/-!

## C. Pure and mixed states

-/

/-- A state is pure when it is an extreme point of the state space. -/
def IsPure (ω : 𝓢[ℝ, E]) : Prop := ω.toLinearMap ∈ stateSpace.extremePoints ℝ

/-- A state is mixed when it isn't pure. -/
def IsMixed (ω : 𝓢[ℝ, E]) : Prop := ¬ ω.IsPure

/-- A state lies in the open segment between two states exactly when it is a genuine (`t ≠ 0, 1`)
mixture of them. -/
lemma mem_openSegment_iff_exists_mix (ω φ ψ : 𝓢[ℝ, E]) :
    ω.toLinearMap ∈ openSegment ℝ φ.toLinearMap ψ.toLinearMap ↔
      ∃ t : unitInterval, t ≠ 0 ∧ t ≠ 1 ∧ mix φ ψ t = ω := by
  constructor
  · rintro ⟨t, s, ht, hs, hts, heq⟩
    have ht1 : t < 1 := by linarith
    let u : unitInterval := ⟨t, ht.le, ht1.le⟩
    refine ⟨u, ?_, ?_, ?_⟩
    · exact ne_of_gt (by exact_mod_cast ht)
    · exact ne_of_lt (by exact_mod_cast ht1)
    · apply toLinearMap_injective
      change t • φ.toLinearMap + (1 - t) • ψ.toLinearMap = ω.toLinearMap
      rwa [show 1 - t = s from by linarith]
  · rintro ⟨t, ht0, ht1, rfl⟩
    refine ⟨(t : ℝ), 1 - (t : ℝ), ?_, ?_, by ring, ?_⟩
    · exact_mod_cast unitInterval.pos_iff_ne_zero.mpr ht0
    · exact sub_pos.mpr (by exact_mod_cast unitInterval.lt_one_iff_ne_one.mpr ht1)
    · rfl

/-- A state is pure exactly when every genuine (`t ≠ 0, 1`) binary decomposition is trivial: both
components already equal it. -/
lemma isPure_iff_forall_mix_eq {ω : 𝓢[ℝ, E]} :
    ω.IsPure ↔ ∀ (φ ψ : 𝓢[ℝ, E]) (t : unitInterval), t ≠ 0 → t ≠ 1 →
      mix φ ψ t = ω → φ = ω ∧ ψ = ω := by
  simp only [IsPure, Set.extremePoints, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨-, hext⟩ φ ψ t ht0 ht1 hmix
    have hseg := (mem_openSegment_iff_exists_mix ω φ ψ).2 ⟨t, ht0, ht1, hmix⟩
    have hseg' : ω.toLinearMap ∈ openSegment ℝ ψ.toLinearMap φ.toLinearMap := by
      rwa [openSegment_symm]
    exact ⟨toLinearMap_injective (hext ⟨φ, rfl⟩ ⟨ψ, rfl⟩ hseg),
      toLinearMap_injective (hext ⟨ψ, rfl⟩ ⟨φ, rfl⟩ hseg')⟩
  · intro h
    refine ⟨⟨ω, rfl⟩, ?_⟩
    rintro x₁ ⟨φ, rfl⟩ x₂ ⟨ψ, rfl⟩ hseg
    obtain ⟨t, ht0, ht1, hmix⟩ := (mem_openSegment_iff_exists_mix ω φ ψ).1 hseg
    exact congrArg (·.toLinearMap) (h φ ψ t ht0 ht1 hmix).1

/-- A genuine mixture equal to a pure state can only repeat that state at both endpoints. -/
lemma IsPure.eq_of_mix {ω φ ψ : 𝓢[ℝ, E]} (hω : ω.IsPure) (t : unitInterval)
    (ht0 : t ≠ 0) (ht1 : t ≠ 1) (hmix : mix φ ψ t = ω) : φ = ω ∧ ψ = ω :=
  isPure_iff_forall_mix_eq.mp hω φ ψ t ht0 ht1 hmix

/-- Purity transported along an injective map sending mixtures to convex combinations: a state
is pure exactly when its image is an extreme point of the image of the state space. -/
lemma isPure_iff_mem_extremePoints {X : Type*} [AddCommGroup X] [Module ℝ X]
    {F : 𝓢[ℝ, E] → X} (hF : Function.Injective F)
    (hmix : ∀ φ ψ t, F (mix φ ψ t) = (t : ℝ) • F φ + (1 - (t : ℝ)) • F ψ) (ω : 𝓢[ℝ, E]) :
    ω.IsPure ↔ F ω ∈ (Set.range F).extremePoints ℝ := by
  rw [isPure_iff_forall_mix_eq, mem_extremePoints]
  refine ⟨fun h => ⟨⟨ω, rfl⟩, ?_⟩, fun h φ ψ t ht0 ht1 hω => ?_⟩
  · rintro _ ⟨φ, rfl⟩ _ ⟨ψ, rfl⟩ ⟨t, s, ht, hs, hts, heq⟩
    obtain rfl : s = 1 - t := by linarith
    obtain ⟨rfl, rfl⟩ := h φ ψ ⟨t, ht.le, by linarith⟩ (fun h => ht.ne' (congrArg Subtype.val h))
      (fun h => hs.ne' (by have : t = 1 := congrArg Subtype.val h; linarith))
      (hF ((hmix _ _ _).trans heq))
    exact ⟨rfl, rfl⟩
  · obtain ⟨h1, h2⟩ := h.2 _ ⟨φ, rfl⟩ _ ⟨ψ, rfl⟩ ⟨t, 1 - t, unitInterval.pos_iff_ne_zero.2 ht0,
      sub_pos.2 (unitInterval.lt_one_iff_ne_one.2 ht1), by ring, by rw [← hmix, hω]⟩
    exact ⟨hF h1, hF h2⟩

/-- A state is mixed exactly when it has a genuine nontrivial binary decomposition. -/
lemma isMixed_iff_exists_mix_ne {ω : 𝓢[ℝ, E]} :
    ω.IsMixed ↔ ∃ (φ ψ : 𝓢[ℝ, E]) (t : unitInterval), t ≠ 0 ∧ t ≠ 1 ∧
      mix φ ψ t = ω ∧ (φ ≠ ω ∨ ψ ≠ ω) := by
  rw [IsMixed, isPure_iff_forall_mix_eq]
  push Not
  simp only [imp_iff_not_or]

end UnitalPositiveLinearMap
