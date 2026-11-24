/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.ProbabilisticTheory.Channel.Basic
public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Topology.UnitInterval

/-!
# Convex spaces of channels

Random choice between channels and convexity of the resulting space of linear maps.

## i. Overview

A random choice between two channels is again a channel: their convex combination preserves
positivity and the certain outcome. Channels therefore form a convex set inside the real
linear maps between their observable spaces. States inherit this construction as channels
into ℝ.

## ii. Key results

- `Channel.mix` : choose between two channels with a specified probability.
- `Channel.channelSpace_convex` : channels form a convex set of linear maps.
- `Channel.mem_openSegment_iff_exists_mix` : genuine mixtures describe open segments.

## iii. Table of contents

- A. Mixing channels
- B. The convex channel space

## iv. References

-/

@[expose] public section

open ProbabilisticTheory unitInterval

namespace Channel

variable {P Q : ProbabilisticTheory}

/-! ## A. Mixing channels -/

/-- Choose the first channel with probability `t` and the second with probability `1 - t`. -/
def mix (Φ Ψ : Channel P Q) (t : unitInterval) : Channel P Q :=
  .ofLinearMap ((t : ℝ) • Φ.toLinearMap + (1 - (t : ℝ)) • Ψ.toLinearMap)
    (fun A hA => add_nonneg (smul_nonneg t.2.1 (map_nonneg Φ hA))
      (smul_nonneg (sub_nonneg.mpr t.2.2) (map_nonneg Ψ hA))) (by simp [← add_smul])

/-- A channel mixture acts by the corresponding convex combination of outputs. -/
@[simp]
lemma mix_apply (Φ Ψ : Channel P Q) (t : unitInterval) (A : P.Observables) :
    mix Φ Ψ t A = (t : ℝ) • Φ A + (1 - (t : ℝ)) • Ψ A := rfl

/-- The linear map of a channel mixture is the same convex combination of linear maps. -/
lemma toLinearMap_mix (Φ Ψ : Channel P Q) (t : unitInterval) :
    (mix Φ Ψ t).toLinearMap = (t : ℝ) • Φ.toLinearMap + (1 - (t : ℝ)) • Ψ.toLinearMap := rfl

/-- Swapping the channels swaps their probabilities. -/
lemma mix_symm (Φ Ψ : Channel P Q) (t : unitInterval) : mix Φ Ψ t = mix Ψ Φ (σ t) := by
  ext A
  simp [mix_apply, add_comm]

/-! ## B. The convex channel space -/

/-- Channels viewed as a subset of the real linear maps between observable spaces. -/
def channelSpace : Set (P.Observables →ₗ[ℝ] Q.Observables) :=
  Set.range (PositiveLinearMap.toLinearMap ∘ toPositiveLinearMap (P := P) (Q := Q))

/-- Channels form a convex set in the space of real linear maps. -/
lemma channelSpace_convex : Convex ℝ (channelSpace (P := P) (Q := Q)) := by
  rw [convex_iff_segment_subset]
  rintro _ ⟨Φ, rfl⟩ _ ⟨Ψ, rfl⟩ x hx
  obtain ⟨t, ht, rfl⟩ := (by rwa [segment_symm, segment_eq_image] at hx)
  exact ⟨mix Φ Ψ ⟨t, ht⟩, by
    simpa only [Function.comp_apply, add_comm] using toLinearMap_mix Φ Ψ ⟨t, ht⟩⟩

/-- Open segments between channels consist exactly of their genuine mixtures. -/
lemma mem_openSegment_iff_exists_mix (Φ Ψ Χ : Channel P Q) :
    Φ.toLinearMap ∈ openSegment ℝ Ψ.toLinearMap Χ.toLinearMap ↔
      ∃ t : unitInterval, 0 < t ∧ t < 1 ∧ mix Ψ Χ t = Φ := by
  rw [openSegment_symm, openSegment_eq_image]
  simp only [Set.mem_image, Set.mem_Ioo, Subtype.exists,
    ← toLinearMap_injective.eq_iff, toLinearMap_mix, add_comm]
  aesop (add safe forward le_of_lt)

end Channel
