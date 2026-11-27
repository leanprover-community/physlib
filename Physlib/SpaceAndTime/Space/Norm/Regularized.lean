/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Physlib.SpaceAndTime.Space.Derivatives.Basic
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
- `normRegularizedPow_neg_two` : For `s = -2` it is `(‖x‖ ^ 2 + ε ^ 2)⁻¹`.
- `inv_norm_sq_add_sq_hasTemperateGrowth` : `(‖x‖ ^ 2 + ε ^ 2)⁻¹` has temperate growth.
- `deriv_normRegularizedPow` : Its derivative in the direction of a basis vector.

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

/-- For `s = -2` the regularized norm power is the inverse of `‖x‖ ^ 2 + ε ^ 2`. -/
lemma normRegularizedPow_neg_two (d : ℕ) (ε : ℝ) :
    normRegularizedPow d ε (-2) = fun x ↦ (‖x‖ ^ 2 + ε ^ 2)⁻¹ := by
  funext x
  simp only [normRegularizedPow]
  rw [show (-2 : ℝ) / 2 = -1 by norm_num, Real.rpow_neg_one]

/-- For `ε ≠ 0` the function `(‖x‖ ^ 2 + ε ^ 2)⁻¹` has temperate growth. -/
lemma inv_norm_sq_add_sq_hasTemperateGrowth {d : ℕ} {ε : ℝ} (hε : ε ≠ 0) :
    (fun x : Space d => (‖x‖ ^ 2 + ε ^ 2)⁻¹).HasTemperateGrowth := by
  have h := normRegularizedPow_hasTemperateGrowth d (Units.mk0 ε hε) (-2)
  rwa [Units.val_mk0, normRegularizedPow_neg_two] at h

/-- The derivative of the regularized norm power in the direction of the basis vector `i`. -/
lemma deriv_normRegularizedPow (d : ℕ) (ε : ℝˣ) (s : ℝ) (i : Fin d) (x : Space d) :
    ∂[i] (normRegularizedPow d ε s) x = s * x i * normRegularizedPow d ε (s - 2) x := by
  have hq : HasFDerivAt (fun x : Space d => ‖x‖ ^ 2 + (ε : ℝ) ^ 2)
      (fderiv ℝ (fun x : Space d => ‖x‖ ^ 2 + (ε : ℝ) ^ 2) x) x :=
    ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.differentiableAt.add_const _).hasFDerivAt
  have hq' : fderiv ℝ (fun x : Space d => ‖x‖ ^ 2 + (ε : ℝ) ^ 2) x (basis i) = 2 * x i := by
    rw [fderiv_add_const, ← Space.deriv_eq, deriv_norm_sq]
  have h := (hq.rpow_const (p := s / 2) (Or.inl (norm_sq_add_unit_sq_pos ε x).ne')).fderiv
  rw [Space.deriv_eq, normRegularizedPow_eq, h]
  simp only [_root_.smul_apply, hq', smul_eq_mul, normRegularizedPow]
  rw [show (s - 2) / 2 = s / 2 - 1 by ring]
  ring

end Space
