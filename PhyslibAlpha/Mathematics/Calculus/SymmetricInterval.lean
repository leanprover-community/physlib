/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-!

# Integrals over a symmetric interval

An even function integrates over `[-τ, τ]` to twice its integral over `[0, τ]`. A convolution with
a continuous weight over `[-τ, τ]` is differentiated under the integral.

## i. Overview

Both statements are used for the radial Bessel kernel. The weight is a continuous real function.
The convolved function is complex valued and continuously differentiable.

## ii. Key results

- `SymmetricInterval.integral_symm_even` : the integral of an even function.
- `SymmetricInterval.hasDerivAt_convolution` : differentiation of a convolution over `[-τ, τ]`.

## iii. Table of contents

- A. Even functions
- B. Convolution

## iv. References

None.

## A. Even functions

- `SymmetricInterval.integral_symm_even` : the integral of an even function.

## B. Convolution

- `SymmetricInterval.hasDerivAt_convolution` : differentiation of a convolution over `[-τ, τ]`.
-/

@[expose] public section

noncomputable section

open MeasureTheory intervalIntegral

namespace SymmetricInterval

/-- The integral of an even continuous function over a symmetric interval. -/
lemma integral_symm_even {f : ℝ → ℂ} (hf : Continuous f) (he : ∀ x, f (-x) = f x) (τ : ℝ) :
    ∫ x in (-τ)..τ, f x = 2 * ∫ x in (0 : ℝ)..τ, f x := by
  have hneg : ∫ x in (-τ)..0, f x = ∫ x in (0 : ℝ)..τ, f x := by
    have := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := τ) f
    simp only [he] at this
    rw [this]
    simp
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0)
    (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _), hneg]
  ring

/-- **Differentiation of a convolution over a bounded interval.** -/
lemma hasDerivAt_convolution {τ : ℝ} (hτ : 0 ≤ τ) (w : ℝ → ℝ) (hw : Continuous w) (f : ℝ → ℂ)
    (hf : ContDiff ℝ 1 f) (ρ : ℝ) :
    HasDerivAt (fun r : ℝ => ∫ u in (-τ)..τ, (w u : ℂ) * f (r + u))
      (∫ u in (-τ)..τ, (w u : ℂ) * deriv f (ρ + u)) ρ := by
  have hfd : Continuous (deriv f) := hf.continuous_deriv (by simp)
  have hfdiff : Differentiable ℝ f := hf.differentiable (by simp)
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := ρ - 1 - τ) (b := ρ + 1 + τ)).exists_bound_of_continuousOn
    hfd.continuousOn
  obtain ⟨W, hW⟩ := (isCompact_Icc (a := -τ) (b := τ)).exists_bound_of_continuousOn
    hw.continuousOn
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun (r : ℝ) (u : ℝ) => (w u : ℂ) * f (r + u))
    (F' := fun (r : ℝ) (u : ℝ) => (w u : ℂ) * deriv f (r + u))
    (bound := fun _ => W * B) (s := Metric.ball ρ 1) (Metric.ball_mem_nhds ρ one_pos)
    ?_ ?_ ?_ ?_ ?_ ?_).2
  · exact Filter.Eventually.of_forall fun r =>
      ((Complex.continuous_ofReal.comp hw).mul (hf.continuous.comp
        (continuous_const.add continuous_id))).aestronglyMeasurable
  · exact (((Complex.continuous_ofReal.comp hw).mul (hf.continuous.comp
      (continuous_const.add continuous_id))).intervalIntegrable _ _)
  · exact ((Complex.continuous_ofReal.comp hw).mul (hfd.comp
      (continuous_const.add continuous_id))).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun u hu x hx => ?_
    rw [Set.uIoc_of_le (by linarith)] at hu
    have hx' := Metric.mem_ball.1 hx
    rw [Real.dist_eq, abs_lt] at hx'
    have h1 := hW u ⟨hu.1.le, hu.2⟩
    have h2 := hB (x + u) ⟨by linarith [hu.1, hx'.1], by linarith [hu.2, hx'.2]⟩
    rw [norm_mul, Complex.norm_real]
    rw [Real.norm_eq_abs] at h1
    have hB0 : 0 ≤ B := (norm_nonneg _).trans h2
    exact mul_le_mul h1 h2 (norm_nonneg _) ((abs_nonneg _).trans h1)
  · exact intervalIntegrable_const
  · refine Filter.Eventually.of_forall fun u _ x _ => ?_
    exact ((hfdiff (x + u)).hasDerivAt.comp_add_const x u).const_mul (w u : ℂ)

end SymmetricInterval
