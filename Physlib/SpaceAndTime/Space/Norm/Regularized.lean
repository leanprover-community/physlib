/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Physlib.SpaceAndTime.Space.Module
/-!

# Regularized powers of the norm on space

## i. Overview

This file contains basic API for regularized powers of the norm on `Space d`, namely
`x ↦ (‖x‖ ^ 2 + ε ^ 2) ^ (s / 2)`.

## ii. Key results

- `normRegularizedPow` : The regularized norm power `x ↦ (‖x‖ ^ 2 + ε ^ 2) ^ (s / 2)`.
- `normRegularizedPow_pos` : Positivity for nonzero regularization parameter.
- `normRegularizedPow_hasTemperateGrowth` : Temperate growth of regularized norm powers.
- `normRegularizedPow_measurable` : Measurability of regularized norm powers.

## iii. Table of contents

- A. Regularized powers of the norm

## iv. References

* None.
-/

@[expose] public section

noncomputable section

namespace Space

open MeasureTheory Function

/-!

## A. Regularized powers of the norm

-/

/-- Power of regularized norm, `(‖x‖² + ε²)^(s/2)`. -/
def normRegularizedPow (d : ℕ) (ε s : ℝ) : Space d → ℝ :=
  fun x ↦ (‖x‖ ^ 2 + ε ^ 2) ^ (s / 2)

lemma normRegularizedPow_eq (d : ℕ) (ε s : ℝ) :
    normRegularizedPow d ε s = fun x ↦ (‖x‖ ^ 2 + ε ^ 2) ^ (s / 2) := rfl

/-- For a nonzero regularization parameter, `‖x‖² + ε²` is positive. -/
lemma norm_sq_add_unit_sq_pos {d : ℕ} (ε : ℝˣ) (x : Space d) : 0 < ‖x‖ ^ 2 + ε ^ 2 :=
    Left.add_pos_of_nonneg_of_pos (sq_nonneg ‖x‖) (sq_pos_iff.mpr <| Units.ne_zero ε)

/-- The regularized norm power is positive for nonzero regularization parameter. -/
lemma normRegularizedPow_pos (d : ℕ) (ε : ℝˣ) (s : ℝ) (x : Space d) :
    0 < normRegularizedPow d ε s x :=
  Real.rpow_pos_of_pos (norm_sq_add_unit_sq_pos ε x) (s / 2)

/-- The regularized norm power has temperate growth. -/
lemma normRegularizedPow_hasTemperateGrowth (d : ℕ) (ε : ℝˣ) (s : ℝ) :
    HasTemperateGrowth (normRegularizedPow d ε s) := by
  let f1 := fun (x : ℝ) ↦ (ε ^ 2) ^ (s / 2) * x
  let f2 := fun (x : Space d) ↦ (1 + ‖x‖ ^ 2) ^ (s / 2)
  let f3 := fun (x : Space d) ↦ ε.1⁻¹ • x
  have h123 : normRegularizedPow d ε s = f1 ∘ f2 ∘ f3 := by
    ext
    simp only [normRegularizedPow, f1, f2, f3, comp_apply, norm_smul, norm_inv, Real.norm_eq_abs]
    rw [← Real.mul_rpow (sq_nonneg ↑ε) (add_nonneg (zero_le_one' _) (sq_nonneg _))]
    simp [mul_add, mul_pow, add_comm]
  rw [h123]
  fun_prop

@[fun_prop]
lemma normRegularizedPow_measurable (d : ℕ) (ε s : ℝ) :
    Measurable (normRegularizedPow d ε s) := by
  rw [normRegularizedPow_eq]
  fun_prop

end Space
