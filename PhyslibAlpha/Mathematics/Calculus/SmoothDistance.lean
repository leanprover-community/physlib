/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Choose.Multinomial

/-!

# A smooth substitute for the distance

The function `sqrt (ε^2 + ‖x - x₀‖^2)` is smooth and bounds the distance.

## i. Overview

The function `sqrt (ε^2 + ‖x - x₀‖^2)` is smooth and bounds the distance. The derivative of
`expNegInvGlue` is continuous.

## ii. Key results

- `smoothDist` : The smooth distance `√(ε² + ‖x - x₀‖²)`.
- `smoothDist_pos`
- `norm_sub_le_smoothDist`
- `continuous_smoothDist`

## iii. Table of contents

- A. The cone weight

## iv. References

None.

## A. The cone weight

- `smoothDist` : The smooth distance `√(ε² + ‖x - x₀‖²)`.

Lemmas: `smoothDist_pos`, `norm_sub_le_smoothDist`, `continuous_smoothDist`,
`hasFDerivAt_smoothDist`, `deriv_expNegInvGlue_nonneg`, `deriv_expNegInvGlue_of_nonpos`,
`continuous_deriv_expNegInvGlue`, `hasDerivAt_expNegInvGlue`.

-/

@[expose] public section

noncomputable section

open scoped InnerProductSpace

namespace SmoothDistance

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The smooth distance `√(ε² + ‖x - x₀‖²)`. -/
def smoothDist (ε : ℝ) (x₀ x : E) : ℝ := √(ε ^ 2 + ‖x - x₀‖ ^ 2)

omit [InnerProductSpace ℝ E] in
lemma smoothDist_pos {ε : ℝ} (hε : 0 < ε) (x₀ x : E) : 0 < smoothDist ε x₀ x :=
  Real.sqrt_pos.2 (by positivity)

omit [InnerProductSpace ℝ E] in
lemma norm_sub_le_smoothDist (ε : ℝ) (x₀ x : E) : ‖x - x₀‖ ≤ smoothDist ε x₀ x := by
  unfold smoothDist
  exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg ε])

omit [InnerProductSpace ℝ E] in
lemma continuous_smoothDist (ε : ℝ) (x₀ : E) : Continuous (smoothDist ε x₀) := by
  unfold smoothDist; fun_prop

lemma hasFDerivAt_smoothDist {ε : ℝ} (hε : 0 < ε) (x₀ x : E) :
    HasFDerivAt (smoothDist ε x₀) ((1 / smoothDist ε x₀ x) • innerSL ℝ (x - x₀)) x := by
  have h1 : HasFDerivAt (fun y : E => ‖y - x₀‖ ^ 2) ((2 : ℝ) • innerSL ℝ (x - x₀)) x := by
    have h2 := ((hasFDerivAt_id x).sub_const x₀).norm_sq
    refine h2.congr_fderiv ?_
    ext h
    simp
  have h3 := (h1.const_add (ε ^ 2)).sqrt (by positivity)
  unfold smoothDist
  convert h3 using 1
  ext h
  simp only [smul_apply, innerSL_apply_apply, smul_eq_mul]
  have : √(ε ^ 2 + ‖x - x₀‖ ^ 2) ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
  field_simp

lemma deriv_expNegInvGlue_nonneg (r : ℝ) : 0 ≤ deriv expNegInvGlue r :=
  expNegInvGlue.monotone.deriv_nonneg

lemma deriv_expNegInvGlue_of_nonpos {r : ℝ} (hr : r ≤ 0) : deriv expNegInvGlue r = 0 := by
  rcases hr.lt_or_eq with h | h
  · have : expNegInvGlue =ᶠ[nhds r] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds h] with y hy
      exact expNegInvGlue.zero_of_nonpos hy.le
    rw [this.deriv_eq]; simp
  · subst h
    refine IsLocalMin.deriv_eq_zero ?_
    refine Filter.Eventually.of_forall fun y => ?_
    rw [expNegInvGlue.zero]
    exact expNegInvGlue.nonneg y

lemma continuous_deriv_expNegInvGlue : Continuous (deriv expNegInvGlue) :=
  (expNegInvGlue.contDiff (n := 1)).continuous_deriv le_rfl

lemma hasDerivAt_expNegInvGlue (r : ℝ) : HasDerivAt expNegInvGlue (deriv expNegInvGlue r) r :=
  ((expNegInvGlue.contDiff (n := 1)).differentiable one_ne_zero r).hasDerivAt
end

end SmoothDistance
