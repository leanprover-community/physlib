/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Tactic.Module
public import Physlib.ProbabilisticTheory.Effect.Basic
public import Physlib.ProbabilisticTheory.OrderUnit.Archimedean

/-!
# The metric space of effects

## i. Overview

Effects sit inside `E`, so pulling back the order-unit norm along the inclusion `Effect E ↪ E`
gives them a metric space structure for free.

Effects also correspond to points of the order-unit-norm ball, by the affine rescaling
`e ↦ 2 • e - 1` that turns `[0, 1]` into the symmetric `[-1, 1]` the norm itself ranges over.

## ii. Key results

- `Effect.dist_eq_orderUnitNorm` : the effect metric is the order-unit norm of the difference.
- `Effect.equivBall` : effects correspond to points of the order-unit-norm ball.

## iii. Table of contents

- A. The effect metric
- B. Effects as points of the order-unit-norm ball

-/

@[expose] public section

open ArchimedeanOrderUnitSpace

variable {E : Type*} [ArchimedeanOrderUnitSpace E]

namespace Effect

/-!

## A. The effect metric

-/

/-- Effects, metrized by the order-unit norm on `E`. -/
noncomputable scoped instance instMetricSpace : MetricSpace (Effect E) :=
  MetricSpace.induced Subtype.val Subtype.val_injective inferInstance

open scoped Effect

lemma dist_eq_orderUnitNorm (e f : Effect E) : dist e f = orderUnitNorm ((e : E) - (f : E)) :=
  dist_eq_norm (e : E) (f : E)

/-!

## B. Effects as points of the order-unit-norm ball

-/

/-- Doubling and re-centering an effect at the order unit lands in the order-unit-norm ball. -/
lemma orderUnitNorm_two_smul_sub_one_le_one (e : Effect E) :
    orderUnitNorm ((2 : ℝ) • (e : E) - 1) ≤ 1 := by
  rw [orderUnitNorm_le_iff]
  refine ⟨by norm_num, ?_, ?_⟩
  · rw [one_smul, ← sub_nonneg,
      show (2 : ℝ) • (e : E) - 1 - -(1 : E) = (2 : ℝ) • (e : E) from by module]
    exact smul_nonneg (by norm_num) e.2.1
  · rw [one_smul, ← sub_nonneg,
      show (1 : E) - ((2 : ℝ) • (e : E) - 1) = (2 : ℝ) • (1 - (e : E)) from by module]
    exact smul_nonneg (by norm_num) (sub_nonneg.mpr e.2.2)

/-- Undoing the re-centering on a point of the order-unit-norm ball gives back an effect. -/
lemma mem_effect_two_inv_smul_one_add (A : {A : E // orderUnitNorm A ≤ 1}) :
    (2 : ℝ)⁻¹ • (1 + (A : E)) ∈ (Effect E : Set E) := by
  obtain ⟨-, hAl, hAu⟩ := orderUnitNorm_le_iff.mp A.2
  rw [one_smul] at hAl hAu
  refine ⟨smul_nonneg (by norm_num) (by simpa using add_le_add (le_refl (1 : E)) hAl), ?_⟩
  have h2 := smul_le_smul_of_nonneg_left (add_le_add (le_refl (1 : E)) hAu)
    (show (0 : ℝ) ≤ (2 : ℝ)⁻¹ by norm_num)
  rw [show (1 : E) + 1 = (2 : ℝ) • (1 : E) from by module] at h2
  rwa [smul_smul, inv_mul_cancel₀ (two_ne_zero), one_smul] at h2

/-- Re-centering, then undoing it, returns the original effect. -/
lemma two_inv_smul_one_add_two_smul_sub_one (e : Effect E) :
    (2 : ℝ)⁻¹ • (1 + ((2 : ℝ) • (e : E) - 1)) = (e : E) := by module

/-- Undoing the re-centering, then redoing it, returns the original ball point. -/
lemma two_smul_two_inv_smul_one_add_sub_one (A : {A : E // orderUnitNorm A ≤ 1}) :
    (2 : ℝ) • ((2 : ℝ)⁻¹ • (1 + (A : E))) - 1 = (A : E) := by
  rw [smul_smul, mul_inv_cancel₀ (two_ne_zero), one_smul]
  module

/-- Effects correspond to points of the order-unit-norm ball by doubling and re-centering at the
order unit: `e ↦ 2 • e - 1`, with inverse `A ↦ (1 + A) / 2`. -/
noncomputable def equivBall : Effect E ≃ {A : E // orderUnitNorm A ≤ 1} where
  toFun e := ⟨(2 : ℝ) • (e : E) - 1, orderUnitNorm_two_smul_sub_one_le_one e⟩
  invFun A := ⟨(2 : ℝ)⁻¹ • (1 + (A : E)), mem_effect_two_inv_smul_one_add A⟩
  left_inv e := Subtype.ext (two_inv_smul_one_add_two_smul_sub_one e)
  right_inv A := Subtype.ext (two_smul_two_inv_smul_one_add_sub_one A)

end Effect
