/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Mathematics.SpecialFunctions.SincPropagator.Series

/-!

# The sine propagation function `t ↦ sin (ω t) / ω`

The function `sincPropagator t ω = sin (ω t) / ω` solves `u'' + ω² u = 0` with `u 0 = 0` and
`u' 0 = 1`.

## i. Overview

The function `sincPropagator t ω = sin (ω t) / ω` solves `u'' + ω² u = 0` with `u 0 = 0` and
`u' 0 = 1`. It is the time dependence of every free wave with frequency `ω`.
Writing it as `t * sinc (ω t)` removes the case `ω = 0`, where it equals `t`.
Together with the cosine it forms the one-parameter group of the harmonic oscillator.
The group law is proved in `Exponential.lean` from the exponential of the generator.

## ii. Key results

- `sincPropagator` : The function `sin (ω t) / ω`, with the value `t` at `ω = 0`.
- `sincPropagator_zero_left`
- `sincPropagator_zero_right`
- `sincPropagator_eq_sin_div`

## iii. Table of contents

- A. The sine propagation function `t ↦ sin (ω t) / ω`
- B. Equivalent forms of the sine propagation function

## iv. References

None.

## A. The sine propagation function `t ↦ sin (ω t) / ω`

- `sincPropagator` : The function `sin (ω t) / ω`, with the value `t` at `ω = 0`.

Lemmas: `sincPropagator_zero_left`, `sincPropagator_zero_right`, `sincPropagator_eq_sin_div`,
`sincPropagator_neg_left`, `abs_sincPropagator_le`, `hasDerivAt_sincPropagator`,
`hasDerivAt_cos_mul`, `continuous_sincPropagator`.

## B. Equivalent forms of the sine propagation function

Lemmas: `sinc_abs`, `sincPropagator_eq_mul_sincSqrt`.

-/

@[expose] public section

noncomputable section

open scoped Nat Interval
open MeasureTheory Set

namespace Real

/-- The function `sin (ω t) / ω`, with the value `t` at `ω = 0`. -/
def sincPropagator (t ω : ℝ) : ℝ := t * sinc (ω * t)

@[simp]
lemma sincPropagator_zero_left (ω : ℝ) : sincPropagator 0 ω = 0 := by simp [sincPropagator]

@[simp]
lemma sincPropagator_zero_right (t : ℝ) : sincPropagator t 0 = t := by simp [sincPropagator]

lemma sincPropagator_eq_sin_div {ω : ℝ} (hω : ω ≠ 0) (t : ℝ) :
    sincPropagator t ω = sin (ω * t) / ω := by
  by_cases ht : t = 0
  · simp [ht]
  · have : ω * t ≠ 0 := mul_ne_zero hω ht
    rw [sincPropagator, sinc_of_ne_zero this]
    field_simp

lemma sincPropagator_neg_left (t ω : ℝ) : sincPropagator (-t) ω = - sincPropagator t ω := by
  simp [sincPropagator, mul_neg, sinc_neg]

lemma abs_sincPropagator_le (t ω : ℝ) : |sincPropagator t ω| ≤ |t| := by
  rw [sincPropagator, abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (abs_sinc_le_one _)

lemma hasDerivAt_sincPropagator (ω t : ℝ) : HasDerivAt (fun s => sincPropagator s ω) (cos (ω * t))
    t := by
  by_cases hω : ω = 0
  · simpa [hω] using hasDerivAt_id' t
  · have h : (fun s => sincPropagator s ω) = fun s => sin (ω * s) / ω := by
      funext s
      exact sincPropagator_eq_sin_div hω s
    rw [h]
    refine (((hasDerivAt_id' t).const_mul ω).sin.div_const ω).congr_deriv ?_
    field_simp

lemma hasDerivAt_cos_mul (ω t : ℝ) :
    HasDerivAt (fun s => cos (ω * s)) (-ω ^ 2 * sincPropagator t ω) t := by
  refine ((hasDerivAt_id' t).const_mul ω).cos.congr_deriv ?_
  by_cases hω : ω = 0
  · simp [hω]
  · rw [sincPropagator_eq_sin_div hω]
    field_simp

lemma continuous_sincPropagator : Continuous fun p : ℝ × ℝ => sincPropagator p.1 p.2 := by
  unfold sincPropagator
  exact continuous_fst.mul (continuous_sinc.comp (continuous_snd.mul continuous_fst))

lemma sinc_abs (x : ℝ) : sinc |x| = sinc x := by
  rcases abs_cases x with ⟨h, _⟩ | ⟨h, _⟩ <;> simp [h, sinc_neg]

lemma sincPropagator_eq_mul_sincSqrt (t ω : ℝ) :
    sincPropagator t ω = t * sincSqrt (t ^ 2 * ω ^ 2) := by
  have h : 0 ≤ t ^ 2 * ω ^ 2 := by positivity
  rw [sincSqrt_of_nonneg h, sincPropagator]
  congr 1
  have : √(t ^ 2 * ω ^ 2) = |ω * t| := by
    rw [show t ^ 2 * ω ^ 2 = (ω * t) ^ 2 by ring]
    exact Real.sqrt_sq_eq_abs _
  rw [this, sinc_abs]

end Real
