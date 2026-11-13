/-
Copyright (c) 2026 Chengyuan AI Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chengyuan AI Lab
-/
module

public import PhyslibAlpha.ClassicalMechanics.OrbitalMechanics.Hohmann.Optimality.Shape

/-!
# Lower bounds on the two Hohmann impulses

Each impulse has a lower bound over the feasible invariant pairs.

## i. Overview

Split the comparison by signed angular momentum relative to the Hohmann value. Factoring the cost
difference gives a sum of nonnegative terms in each case.

## ii. Key results

- `first_square_lower_bound` gives the main result of this module.

## iii. Table of contents

- A. The two squared cost inequalities

## iv. References

- [ref: hohmann_prussing_1992]. Prussing studies the two-impulse global comparison.
-/

@[expose] public noncomputable section

namespace ClassicalMechanics.HohmannOptimality

/-!
## A. The two squared cost inequalities
-/
open Shape

/-- Exact nonnegative certificate on the h ≤ hH half-plane. -/
lemma gap₁_low (s : Shape) (w h : ℝ) :
    s.burnSquare₁ w h - s.burnH₁ ^ 2 =
      (w + 2*s.alpha - s.alpha^2*h^2) +
      (s.hH-h)*(2-s.alpha^2*(h+s.hH)) := by
  dsimp [burnSquare₁, burnH₁]
  nlinarith [s.corner_relation]

lemma gap₁_high (s : Shape) (w h : ℝ) :
    s.burnSquare₁ w h - s.burnH₁ ^ 2 =
      (w+2-h^2) + (h-s.hH)*(h+s.hH-2) := by
  dsimp [burnSquare₁, burnH₁]
  ring

lemma gap₂_low (s : Shape) (w h : ℝ) :
    s.burnSquare₂ w h - s.burnH₂ ^ 2 =
      (w+2*s.alpha-s.alpha^2*h^2) +
      s.alpha*(s.hH-h)*(2*s.circularOuter-s.alpha*(h+s.hH)) := by
  dsimp [burnSquare₂, burnH₂]
  nlinarith [s.c_sq]

lemma gap₂_high (s : Shape) (w h : ℝ) :
    s.burnSquare₂ w h - s.burnH₂ ^ 2 =
      (w+2-h^2) + (h-s.hH)*(h+s.hH-2*s.alpha*s.circularOuter) := by
  dsimp [burnSquare₂, burnH₂]
  nlinarith [s.c_sq, s.corner_relation]

lemma low_factor₁_pos (s : Shape) {h : ℝ} (hh : h ≤ s.hH) :
    0 < 2 - s.alpha^2*(h+s.hH) := by
  have hm := mul_le_mul_of_nonneg_left hh (sq_nonneg s.alpha)
  nlinarith [s.alpha_sq_h_lt_one]
lemma low_factor₂_pos (s : Shape) {h : ℝ} (hh : h ≤ s.hH) :
    0 < 2*s.circularOuter-s.alpha*(h+s.hH) := by
  have hm := mul_le_mul_of_nonneg_left hh (le_of_lt s.alpha_pos)
  nlinarith [s.alpha_h_lt_c]
lemma high_factor₁_pos (s : Shape) {h : ℝ} (hh : s.hH ≤ h) :
    0 < h+s.hH-2 := by linarith [s.one_lt_h]
lemma high_factor₂_pos (s : Shape) {h : ℝ} (hh : s.hH ≤ h) :
    0 < h+s.hH-2*s.alpha*s.circularOuter := by linarith [s.alpha_c_lt_h]

/-- Every feasible competitor pays at least the Hohmann first impulse. -/
lemma first_square_lower_bound (s : Shape) {w h : ℝ} (hf : s.Feasible w h) :
    s.burnH₁ ^ 2 ≤ s.burnSquare₁ w h := by
  by_cases hh : h ≤ s.hH
  · have hp := mul_nonneg (sub_nonneg.mpr hh) (le_of_lt (low_factor₁_pos s hh))
    have hs := sub_nonneg.mpr hf.2
    have hid := gap₁_low s w h
    linarith
  · have hh' : s.hH ≤ h := le_of_lt (lt_of_not_ge hh)
    have hp := mul_nonneg (sub_nonneg.mpr hh') (le_of_lt (high_factor₁_pos s hh'))
    have hs := sub_nonneg.mpr hf.1
    have hid := gap₁_high s w h
    linarith

/-- The second impulse separately also attains its global minimum at Hohmann. -/
lemma second_square_lower_bound (s : Shape) {w h : ℝ} (hf : s.Feasible w h) :
    s.burnH₂ ^ 2 ≤ s.burnSquare₂ w h := by
  by_cases hh : h ≤ s.hH
  · have hp := mul_nonneg
      (mul_nonneg (le_of_lt s.alpha_pos) (sub_nonneg.mpr hh))
      (le_of_lt (low_factor₂_pos s hh))
    have hs := sub_nonneg.mpr hf.2
    have hid := gap₂_low s w h
    linarith
  · have hh' : s.hH ≤ h := le_of_lt (lt_of_not_ge hh)
    have hp := mul_nonneg (sub_nonneg.mpr hh') (le_of_lt (high_factor₂_pos s hh'))
    have hs := sub_nonneg.mpr hf.1
    have hid := gap₂_high s w h
    linarith

lemma first_square_strict_of_h_ne (s : Shape) {w h : ℝ}
    (hf : s.Feasible w h) (hne : h ≠ s.hH) :
    s.burnH₁ ^ 2 < s.burnSquare₁ w h := by
  rcases lt_or_gt_of_ne hne with hh | hh
  · have hp := mul_pos (sub_pos.mpr hh) (low_factor₁_pos s (le_of_lt hh))
    have hid := gap₁_low s w h
    linarith [hf.2]
  · have hp := mul_pos (sub_pos.mpr hh) (high_factor₁_pos s (le_of_lt hh))
    have hid := gap₁_high s w h
    linarith [hf.1]

/-- The unique minimizer is an invariant pair, not a unique time-parametrized
trajectory: rotations and extra revolutions still have the same cost. -/
lemma invariant_pair_of_first_square_eq (s : Shape) {w h : ℝ}
    (hf : s.Feasible w h) (heq : s.burnSquare₁ w h = s.burnH₁^2) :
    h = s.hH ∧ w = s.energyH := by
  have hh : h = s.hH := by
    by_contra hn
    have hs := first_square_strict_of_h_ne s hf hn
    linarith
  refine ⟨hh, ?_⟩
  rw [hh] at heq
  dsimp [burnSquare₁, burnH₁, energyH] at *
  nlinarith

end ClassicalMechanics.HohmannOptimality
