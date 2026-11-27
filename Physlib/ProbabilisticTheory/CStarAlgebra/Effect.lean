/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Analysis.CStarAlgebra.Extreme
public import Physlib.ProbabilisticTheory.CStarAlgebra.Basic
public import Physlib.ProbabilisticTheory.Effect.Sharp

/-!
# Effects of a C⋆-algebra

The sharp effects of a C⋆-algebra are exactly its projections.

## i. Overview

An effect is an observable between `0` and the order unit `1`. The effects form a convex set and
the sharp effects are its extreme points. They are no nontrivial mixtures of other effects.

In a C⋆-algebra the sharp effects are exactly the projections, the elements `P` with
`P = P⋆ = P²`.

## ii. Key results

- `ProbabilisticTheory.Effect.ofProjection` : a projection as an effect.
- `ProbabilisticTheory.Effect.isSharp_iff_isStarProjection` : an effect is sharp exactly when it
  is a projection.
- `ProbabilisticTheory.Effect.projectionOrderIso` : the sharp effects are exactly the projections.

## iii. Table of contents

- A. Projections as effects
- B. Sharp effects are projections

## iv. References

* None.

-/

@[expose] public section

open Set Metric

namespace ProbabilisticTheory.Effect

variable {𝒜 : Type*} [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]

/-! ## A. Projections as effects -/

/-- A projection `P` as an effect. -/
def ofProjection {P : 𝒜} (hP : IsStarProjection P) : Effect (ofCStarAlgebra 𝒜) :=
  ⟨⟨P, hP.isSelfAdjoint⟩, hP.nonneg, hP.le_one⟩

@[simp]
lemma coe_ofProjection {P : 𝒜} (hP : IsStarProjection P) :
    (ofProjection hP : 𝒜) = P := rfl

/-! ## B. Sharp effects are projections -/

/-- An element lies in the positive part of the unit ball exactly when it is an effect. -/
lemma mem_nonneg_inter_closedBall_iff (x : selfAdjoint 𝒜) :
    (x : 𝒜) ∈ {a : 𝒜 | 0 ≤ a} ∩ closedBall 0 1 ↔ x ∈ Effect (ofCStarAlgebra 𝒜) := by
  rw [mem_inter_iff, mem_closedBall_zero_iff, mem_ofPred_eq]
  refine and_congr_right ?_
  intro hx
  exact CStarAlgebra.norm_le_one_iff_of_nonneg (x : 𝒜) hx

/-- The effects are the positive part of the unit ball. -/
lemma image_coe_eq_nonneg_inter_closedBall :
    (selfAdjoint.submodule ℝ 𝒜).subtype '' Effect (ofCStarAlgebra 𝒜) =
      {a : 𝒜 | 0 ≤ a} ∩ closedBall 0 1 := by
  ext a
  refine ⟨?_, ?_⟩
  · rintro ⟨x, hx, rfl⟩
    exact (mem_nonneg_inter_closedBall_iff x).mpr hx
  · intro ha
    exact ⟨⟨a, IsSelfAdjoint.of_nonneg ha.1⟩, (mem_nonneg_inter_closedBall_iff _).mp ha, rfl⟩

/-- An effect of a C⋆-algebra is sharp exactly when it is a projection. -/
lemma isSharp_iff_isStarProjection (e : Effect (ofCStarAlgebra 𝒜)) :
    IsSharp e ↔ IsStarProjection (e : 𝒜) := by
  have key {f : selfAdjoint 𝒜 →ₗ[ℝ] 𝒜} (hf : Function.Injective f) {s : Set (selfAdjoint 𝒜)}
      {x : selfAdjoint 𝒜} : f x ∈ extremePoints ℝ (f '' s) ↔ x ∈ extremePoints ℝ s := by
    have h (a b : selfAdjoint 𝒜) : f '' openSegment ℝ a b = openSegment ℝ (f a) (f b) :=
      image_openSegment ℝ f.toAffineMap a b
    simp only [mem_extremePoints_iff_left, hf.mem_set_image, forall_mem_image, ← h, hf.eq_iff]
  rw [isStarProjection_iff_mem_extremePoints_setOfPred_nonneg_inter_unitClosedBall,
    ← image_coe_eq_nonneg_inter_closedBall, IsSharp]
  exact (key (selfAdjoint.submodule ℝ 𝒜).injective_subtype).symm

/-- The effect of a projection is sharp. -/
lemma isSharp_ofProjection {P : 𝒜} (hP : IsStarProjection P) : IsSharp (ofProjection hP) :=
  (isSharp_iff_isStarProjection _).mpr hP

/-- The sharp effects of a C⋆-algebra are exactly its projections. -/
def projectionOrderIso :
    {P : 𝒜 // IsStarProjection P} ≃o {e : Effect (ofCStarAlgebra 𝒜) // IsSharp e} where
  toFun P := ⟨ofProjection P.2, isSharp_ofProjection P.2⟩
  invFun e := ⟨e.1, (isSharp_iff_isStarProjection _).mp e.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

end ProbabilisticTheory.Effect
