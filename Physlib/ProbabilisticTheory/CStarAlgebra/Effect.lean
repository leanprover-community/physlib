/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Analysis.CStarAlgebra.Extreme
public import Physlib.ProbabilisticTheory.CStarAlgebra.OrderUnit
public import Physlib.ProbabilisticTheory.Effect.Sharp

/-!
# Sharp effects of a C⋆-algebra

The sharp effects of a C⋆-algebra are exactly its projections.

## i. Overview

An effect is a measurement with two outcomes, yes and no. Every state gives the outcome yes a
probability. Sharp effects are the extreme points of the convex set of effects. They are no
nontrivial mixtures of other effects.

In a C⋆-algebra the sharp effects are exactly the projections `P`. These satisfy `P = P⋆ = P²`.
They describe projective yes-no measurements. Each outcome is `0` or `1`. Its probability still
depends on the state.

## ii. Key results

- `IsStarProjection.toEffect` : a projection as an effect.
- `ProbabilisticTheory.Effect.isSharp_iff_isStarProjection` : the sharp effects are exactly the
  projections.

## iii. Table of contents

- A. Projections as effects
- B. Sharp effects are projections

## iv. References

* None.

-/

@[expose] public section

open Set Metric

variable {𝒜 : Type*} [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]

/-! ## A. Projections as effects -/

namespace IsStarProjection

/-- A projection as an effect: the yes-no measurement whose outcome yes is `P`. -/
def toEffect {P : 𝒜} (hP : IsStarProjection P) : ProbabilisticTheory.Effect (selfAdjoint 𝒜) :=
  ⟨⟨P, hP.isSelfAdjoint⟩, hP.nonneg, hP.le_one⟩

@[simp]
lemma coe_toEffect {P : 𝒜} (hP : IsStarProjection P) :
    ((hP.toEffect : selfAdjoint 𝒜) : 𝒜) = P := rfl

end IsStarProjection

/-! ## B. Sharp effects are projections -/

/-- An injective linear map preserves and reflects extreme points. -/
lemma LinearMap.mem_extremePoints_image_iff {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] {f : E →ₗ[ℝ] F} (hf : Function.Injective f) {s : Set E}
    {x : E} : f x ∈ extremePoints ℝ (f '' s) ↔ x ∈ extremePoints ℝ s := by
  have h (a b : E) : f '' openSegment ℝ a b = openSegment ℝ (f a) (f b) :=
    image_openSegment ℝ f.toAffineMap a b
  simp only [mem_extremePoints_iff_left, hf.mem_set_image, forall_mem_image, ← h, hf.eq_iff]

namespace ProbabilisticTheory.Effect

/-- An element lies in the positive part of the unit ball exactly when it is an effect. -/
lemma mem_nonneg_inter_closedBall_iff (x : selfAdjoint 𝒜) :
    (x : 𝒜) ∈ {a : 𝒜 | 0 ≤ a} ∩ closedBall 0 1 ↔ x ∈ Effect (selfAdjoint 𝒜) := by
  rw [mem_inter_iff, mem_closedBall_zero_iff, mem_ofPred_eq]
  refine and_congr_right ?_
  intro hx
  exact CStarAlgebra.norm_le_one_iff_of_nonneg (x : 𝒜) hx

/-- The effects are the positive part of the unit ball. -/
lemma image_coe_eq_nonneg_inter_closedBall :
    (selfAdjoint.submodule ℝ 𝒜).subtype '' Effect (selfAdjoint 𝒜) =
      {a : 𝒜 | 0 ≤ a} ∩ closedBall 0 1 := by
  ext a
  refine ⟨?_, ?_⟩
  · rintro ⟨x, hx, rfl⟩
    exact (mem_nonneg_inter_closedBall_iff x).mpr hx
  · intro ha
    exact ⟨⟨a, IsSelfAdjoint.of_nonneg ha.1⟩, (mem_nonneg_inter_closedBall_iff _).mp ha, rfl⟩

/-- An effect of a C⋆-algebra is sharp exactly when it is a projection. -/
lemma isSharp_iff_isStarProjection (e : Effect (selfAdjoint 𝒜)) :
    IsSharp e ↔ IsStarProjection ((e : selfAdjoint 𝒜) : 𝒜) := by
  rw [isStarProjection_iff_mem_extremePoints_setOfPred_nonneg_inter_unitClosedBall,
    ← image_coe_eq_nonneg_inter_closedBall, IsSharp]
  exact (LinearMap.mem_extremePoints_image_iff Subtype.val_injective).symm

/-- The effect of a projection is sharp. -/
lemma isSharp_toEffect {P : 𝒜} (hP : IsStarProjection P) : IsSharp hP.toEffect :=
  (isSharp_iff_isStarProjection _).mpr hP

end ProbabilisticTheory.Effect
