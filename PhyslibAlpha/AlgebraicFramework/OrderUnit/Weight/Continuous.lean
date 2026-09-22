/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.OrderUnit.Weight.Extension
public import PhyslibAlpha.AlgebraicFramework.OrderUnit.Norm
public import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap

/-!

# Continuous dual realization of finite weights

Positive functionals are automatically bounded for the order-unit norm.  Combining this fact
with the unique extension of a finite weight realizes every finite weight as a continuous linear
functional on `WithOrderUnitNorm E`.

-/

@[expose] public section

open IsArchimedeanOrderUnit

variable {E : Type*} [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E] [Module ℝ E]
  [PosSMulMono ℝ E] [One E] [IsArchimedeanOrderUnit E]

namespace PositiveLinearMap

/-- A positive functional is order-unit-norm bounded, with bound given by its value at the order
unit.  For a normalized positive functional this specializes to the contractive state bound. -/
lemma abs_apply_le_apply_one_mul_orderUnitNorm (f : E →ₚ[ℝ] ℝ) (x : E) :
    |f x| ≤ f 1 * orderUnitNorm x := by
  have hb := orderUnitNorm_mem_orderUnitBounds x
  have hl := f.monotone' hb.2.1
  have hu := f.monotone' hb.2.2
  have hl' : -(orderUnitNorm x * f 1) ≤ f x := by
    change f (-(orderUnitNorm x • (1 : E))) ≤ f x at hl
    rw [_root_.map_neg, map_smul, smul_eq_mul] at hl
    exact hl
  have hu' : f x ≤ orderUnitNorm x * f 1 := by
    change f x ≤ f (orderUnitNorm x • (1 : E)) at hu
    rw [map_smul, smul_eq_mul] at hu
    exact hu
  rw [mul_comm]
  exact abs_le.mpr ⟨hl', hu'⟩

/-- A positive functional as a continuous functional on the canonical order-unit-norm copy. -/
noncomputable def toOrderUnitContinuousLinearMap (f : E →ₚ[ℝ] ℝ) :
    WithOrderUnitNorm E →L[ℝ] ℝ :=
  f.toLinearMap.mkContinuous (f 1) fun x => by
    rw [Real.norm_eq_abs, WithOrderUnitNorm.norm_eq_orderUnitNorm]
    exact f.abs_apply_le_apply_one_mul_orderUnitNorm x

@[simp]
lemma toOrderUnitContinuousLinearMap_apply (f : E →ₚ[ℝ] ℝ) (x : E) :
    f.toOrderUnitContinuousLinearMap x = f x := rfl

end PositiveLinearMap

namespace Weight.IsFinite

/-- The canonical continuous linear extension of a finite weight to the order-unit-norm copy. -/
noncomputable def toOrderUnitContinuousLinearMap {w : Weight E} (hw : w.IsFinite) :
    WithOrderUnitNorm E →L[ℝ] ℝ := hw.toPositiveLinearMap.toOrderUnitContinuousLinearMap

@[simp]
lemma toOrderUnitContinuousLinearMap_apply_of_nonneg {w : Weight E} (hw : w.IsFinite)
    (x : PosCone E) :
    hw.toOrderUnitContinuousLinearMap (x : E) = (w x).toReal := by
  rw [toOrderUnitContinuousLinearMap, PositiveLinearMap.toOrderUnitContinuousLinearMap_apply,
    toPositiveLinearMap_apply_of_nonneg]

end Weight.IsFinite
