/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-!

# `cos √y` and `sinc √y` as entire functions

The functions `cos √y` and `sinc √y` are even in `√y`.

## i. Overview

The functions `cos √y` and `sinc √y` are even in `√y`. They are therefore power series in `y` with
infinite radius, and smooth on all of `ℝ` although `√` is not differentiable at `0`.
This file defines them by their series and proves that they are smooth.
It then proves that every derivative is bounded by `2⁻ʲ` on `[0, ∞)`.

## ii. Key results

- `sqrtCoeff` : coefficients `(-1)ⁿ / (2n + k)!`
- `cosSqrt` : `cos √y` as an entire function of `y`.
- `sincSqrt` : `sinc √y` as an entire function of `y`.
- `abs_iteratedDeriv_le` : All derivatives of `cos √y` and `sinc √y` are bounded by `2⁻ʲ` on
  `[0, ∞)`.

## iii. Table of contents

- A. `cos √y` and `sinc √y` as entire functions

## iv. References

None.

## A. `cos √y` and `sinc √y` as entire functions

- `sqrtCoeff` : coefficients `(-1)ⁿ / (2n + k)!`
- `cosSqrt` : `cos √y` as an entire function of `y`.
- `sincSqrt` : `sinc √y` as an entire function of `y`.

Lemmas: `radius_sqrtCoeff`, `cosSqrt_eq_sum`, `sincSqrt_eq_sum`, `analyticOnNhd_sqrtSum`,
`contDiff_cosSqrt`, `contDiff_sincSqrt`, `sqrt_pow_two_mul`, `cosSqrt_of_nonneg`,
`sincSqrt_of_nonneg`, `analyticOnNhd_cosSqrt` and more.

-/

@[expose] public section

noncomputable section

open scoped Nat Interval
open FormalMultilinearSeries Filter Topology MeasureTheory Set

namespace Real

/-- coefficients `(-1)ⁿ / (2n + k)!` -/
def sqrtCoeff (k n : ℕ) : ℝ := (-1) ^ n / (2 * n + k)!

lemma radius_sqrtCoeff (k : ℕ) : (ofScalars ℝ (sqrtCoeff k)).radius = ⊤ := by
  refine ofScalars_radius_eq_top_of_tendsto ℝ _ ?_ ?_
  · exact Eventually.of_forall fun n => by simp [sqrtCoeff, Nat.factorial_ne_zero]
  · have h : ∀ n : ℕ, ‖sqrtCoeff k n.succ‖ / ‖sqrtCoeff k n‖ =
        1 / (((2*n+k+1)*(2*n+k+2) : ℕ) : ℝ) := by
      intro n
      simp only [sqrtCoeff, norm_div, norm_pow, norm_neg, norm_one, one_pow, Real.norm_natCast]
      have e : 2 * n.succ + k = (2*n+k+1)+1 := by omega
      rw [e, Nat.factorial_succ, Nat.factorial_succ]
      push_cast
      have := Nat.factorial_pos (2*n+k)
      field_simp
      ring
    simp_rw [h]
    refine tendsto_const_nhds.div_atTop ?_
    refine tendsto_natCast_atTop_atTop.comp (tendsto_atTop_mono (fun n => ?_) tendsto_id)
    show n ≤ _
    nlinarith

/-- `cos √y` as an entire function of `y`. -/
def cosSqrt (y : ℝ) : ℝ := ∑' n, sqrtCoeff 0 n * y ^ n

/-- `sinc √y` as an entire function of `y`. -/
def sincSqrt (y : ℝ) : ℝ := ∑' n, sqrtCoeff 1 n * y ^ n

lemma cosSqrt_eq_sum : cosSqrt = ofScalarsSum (E := ℝ) (sqrtCoeff 0) := by
  funext y; simp [cosSqrt, ofScalarsSum_eq_tsum]

lemma sincSqrt_eq_sum : sincSqrt = ofScalarsSum (E := ℝ) (sqrtCoeff 1) := by
  funext y; simp [sincSqrt, ofScalarsSum_eq_tsum]

lemma analyticOnNhd_sqrtSum (k : ℕ) : AnalyticOnNhd ℝ (ofScalarsSum (E := ℝ) (sqrtCoeff k))
    Set.univ := by
  have hr : 0 < (ofScalars ℝ (sqrtCoeff k)).radius := by rw [radius_sqrtCoeff]; simp
  have h := (ofScalars ℝ (sqrtCoeff k)).hasFPowerSeriesOnBall hr
  rw [radius_sqrtCoeff] at h
  intro y _
  exact h.analyticOnNhd y (by simp)

lemma contDiff_cosSqrt : ContDiff ℝ ⊤ cosSqrt := by
  rw [cosSqrt_eq_sum]; exact (analyticOnNhd_sqrtSum 0).contDiff

lemma contDiff_sincSqrt : ContDiff ℝ ⊤ sincSqrt := by
  rw [sincSqrt_eq_sum]; exact (analyticOnNhd_sqrtSum 1).contDiff

lemma sqrt_pow_two_mul {y : ℝ} (hy : 0 ≤ y) (n : ℕ) : √y ^ (2 * n) = y ^ n := by
  rw [pow_mul, Real.sq_sqrt hy]

lemma cosSqrt_of_nonneg {y : ℝ} (hy : 0 ≤ y) : cosSqrt y = cos (√y) := by
  rw [← (Real.hasSum_cos (√y)).tsum_eq, cosSqrt]
  refine tsum_congr fun n => ?_
  rw [sqrt_pow_two_mul hy]
  simp [sqrtCoeff, div_eq_mul_inv, mul_comm, mul_left_comm]

lemma sincSqrt_of_nonneg {y : ℝ} (hy : 0 ≤ y) : sincSqrt y = sinc (√y) := by
  rcases hy.eq_or_lt with rfl | hpos
  · rw [sincSqrt, tsum_eq_single 0]
    · simp [sqrtCoeff]
    · intro n hn; simp [hn]
  · have hr : √y ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
    rw [sinc_of_ne_zero hr, ← (Real.hasSum_sin (√y)).tsum_eq, ← tsum_div_const, sincSqrt]
    refine tsum_congr fun n => ?_
    have : √y ^ (2 * n + 1) = √y ^ (2 * n) * √y := pow_succ _ _
    rw [this, sqrt_pow_two_mul hpos.le]
    simp only [sqrtCoeff]
    field_simp

lemma analyticOnNhd_cosSqrt : AnalyticOnNhd ℝ cosSqrt Set.univ := by
  rw [cosSqrt_eq_sum]; exact analyticOnNhd_sqrtSum 0

lemma analyticOnNhd_sincSqrt : AnalyticOnNhd ℝ sincSqrt Set.univ := by
  rw [sincSqrt_eq_sum]; exact analyticOnNhd_sqrtSum 1

lemma hasDerivAt_cosSqrt_of_pos {y : ℝ} (hy : 0 < y) :
    HasDerivAt cosSqrt (-(1 / 2) * sincSqrt y) y := by
  have hev : cosSqrt =ᶠ[nhds y] fun z => cos (√z) := by
    filter_upwards [lt_mem_nhds hy] with z hz using cosSqrt_of_nonneg hz.le
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  have hr : √y ≠ 0 := (Real.sqrt_pos.2 hy).ne'
  refine (Real.hasDerivAt_sqrt hy.ne').cos.congr_deriv ?_
  rw [sincSqrt_of_nonneg hy.le, sinc_of_ne_zero hr]
  field_simp

lemma deriv_cosSqrt : deriv cosSqrt = fun y => -(1 / 2) * sincSqrt y := by
  have h1 : AnalyticOnNhd ℝ (deriv cosSqrt) Set.univ := analyticOnNhd_cosSqrt.deriv
  have h2 : AnalyticOnNhd ℝ (fun y => -(1 / 2) * sincSqrt y) Set.univ :=
    analyticOnNhd_const.mul analyticOnNhd_sincSqrt
  have := h1.eqOn_of_preconnected_of_eventuallyEq h2 isPreconnected_univ
    (Set.mem_univ (1 : ℝ)) (by
      filter_upwards [lt_mem_nhds (zero_lt_one' ℝ)] with z hz
      exact (hasDerivAt_cosSqrt_of_pos hz).deriv)
  exact funext fun y => this (Set.mem_univ y)

lemma cosSqrt_eq_sincSqrt_add_of_pos {y : ℝ} (hy : 0 < y) :
    cosSqrt y = sincSqrt y + 2 * y * deriv sincSqrt y := by
  have hr : √y ≠ 0 := (Real.sqrt_pos.2 hy).ne'
  have hev : sincSqrt =ᶠ[nhds y] fun z => sin (√z) / √z := by
    filter_upwards [lt_mem_nhds hy] with z hz
    rw [sincSqrt_of_nonneg hz.le, sinc_of_ne_zero (Real.sqrt_pos.2 hz).ne']
  have hd : HasDerivAt sincSqrt
      ((cos (√y) * (1 / (2 * √y)) * √y - sin (√y) * (1 / (2 * √y))) / √y ^ 2) y :=
    HasDerivAt.congr_of_eventuallyEq
      (((Real.hasDerivAt_sqrt hy.ne').sin).div (Real.hasDerivAt_sqrt hy.ne') hr) hev
  rw [hd.deriv, sincSqrt_of_nonneg hy.le, sinc_of_ne_zero hr, cosSqrt_of_nonneg hy.le]
  have : y = √y ^ 2 := (Real.sq_sqrt hy.le).symm
  rw [this, Real.sqrt_sq (Real.sqrt_nonneg _)]
  field_simp
  ring

lemma hasDerivAt_integral_scale {G : ℝ → ℝ} (hG : ContDiff ℝ 1 G) (k : ℕ) (y : ℝ) :
    HasDerivAt (fun y => ∫ u in (0:ℝ)..1, u ^ k * G (u ^ 2 * y))
      (∫ u in (0:ℝ)..1, u ^ (k + 2) * deriv G (u ^ 2 * y)) y := by
  have hGd : Continuous (deriv G) := hG.continuous_deriv_one
  have hGc : Continuous G := hG.continuous
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := -(|y| + 1)) (b := |y| + 1)).exists_bound_of_continuousOn
    hGd.continuousOn
  have key : ∀ u ∈ Ι (0:ℝ) 1, ∀ x ∈ Metric.ball y 1,
      ‖u ^ (k + 2) * deriv G (u ^ 2 * x)‖ ≤ B := by
    intro u hu x hx
    rw [uIoc_of_le zero_le_one] at hu
    have hu0 : 0 ≤ u := hu.1.le
    have hu1 : u ≤ 1 := hu.2
    have hu2 : u ^ 2 ≤ 1 := by nlinarith
    have hu3 : u ^ (k + 2) ≤ 1 := pow_le_one₀ hu0 hu1
    have hxb : |x| ≤ |y| + 1 := by
      have := Metric.mem_ball.1 hx
      rw [Real.dist_eq] at this
      calc |x| = |(x - y) + y| := by ring_nf
        _ ≤ |x - y| + |y| := abs_add_le _ _
        _ ≤ |y| + 1 := by linarith
    have hmem : u ^ 2 * x ∈ Icc (-(|y| + 1)) (|y| + 1) := by
      rw [mem_Icc, ← abs_le]
      calc |u ^ 2 * x| = u ^ 2 * |x| := by rw [abs_mul, abs_of_nonneg (sq_nonneg u)]
        _ ≤ 1 * |x| := by gcongr
        _ ≤ |y| + 1 := by linarith
    calc ‖u ^ (k + 2) * deriv G (u ^ 2 * x)‖ = u ^ (k + 2) * ‖deriv G (u ^ 2 * x)‖ := by
          rw [norm_mul, Real.norm_of_nonneg (pow_nonneg hu0 _)]
      _ ≤ 1 * B := by
          have := hB _ hmem
          exact mul_le_mul hu3 this (norm_nonneg _) zero_le_one
      _ = B := one_mul B
  have := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun (x u : ℝ) => u ^ k * G (u ^ 2 * x))
    (F' := fun x u => u ^ (k + 2) * deriv G (u ^ 2 * x))
    (x₀ := y) (s := Metric.ball y 1) (a := 0) (b := 1) (μ := volume) (bound := fun _ => B)
    (Metric.ball_mem_nhds y one_pos)
    (Eventually.of_forall fun x =>
      (by fun_prop : Continuous fun u : ℝ => u ^ k * G (u ^ 2 * x)).aestronglyMeasurable)
    ((by fun_prop : Continuous fun u : ℝ => u ^ k * G (u ^ 2 * y)).intervalIntegrable _ _)
    (by exact (by fun_prop : Continuous fun u : ℝ =>
      u ^ (k + 2) * deriv G (u ^ 2 * y)).aestronglyMeasurable)
    (Eventually.of_forall key)
    intervalIntegrable_const
    (Eventually.of_forall fun u _ x _ => by
      have h1 : HasDerivAt G (deriv G (u ^ 2 * x)) (u ^ 2 * x) :=
        ((hG.differentiable one_ne_zero) _).hasDerivAt
      have h2 : HasDerivAt (fun x : ℝ => u ^ 2 * x) (u ^ 2) x := by
        simpa using (hasDerivAt_id x).const_mul (u ^ 2)
      have := (h1.comp x h2).const_mul (u ^ k)
      exact this.congr_deriv (by ring))
  exact this.2

lemma cosSqrt_eq_sincSqrt_add (y : ℝ) :
    cosSqrt y = sincSqrt y + 2 * y * deriv sincSqrt y := by
  have h1 : AnalyticOnNhd ℝ cosSqrt Set.univ := analyticOnNhd_cosSqrt
  have h2 : AnalyticOnNhd ℝ (fun y => sincSqrt y + 2 * y * deriv sincSqrt y) Set.univ :=
    analyticOnNhd_sincSqrt.add
      ((analyticOnNhd_const.mul analyticOnNhd_id).mul analyticOnNhd_sincSqrt.deriv)
  exact h1.eqOn_of_preconnected_of_eventuallyEq h2 isPreconnected_univ
    (Set.mem_univ (1 : ℝ)) (by
      filter_upwards [lt_mem_nhds (zero_lt_one' ℝ)] with z hz
      exact cosSqrt_eq_sincSqrt_add_of_pos hz) (Set.mem_univ y)

/-- `sinc √y` is the mean of `cos √(u² y)`. -/
lemma sincSqrt_eq_integral (y : ℝ) :
    sincSqrt y = ∫ u in (0:ℝ)..1, cosSqrt (u ^ 2 * y) := by
  have hd : ∀ u ∈ uIcc (0:ℝ) 1, HasDerivAt (fun u => u * sincSqrt (u ^ 2 * y))
      (cosSqrt (u ^ 2 * y)) u := by
    intro u _
    have h1 : HasDerivAt sincSqrt (deriv sincSqrt (u ^ 2 * y)) (u ^ 2 * y) :=
      ((contDiff_sincSqrt.differentiable (by simp)) _).hasDerivAt
    have h2 : HasDerivAt (fun u : ℝ => u ^ 2 * y) (2 * u * y) u := by
      simpa using ((hasDerivAt_pow 2 u).mul_const y)
    have h3 := (hasDerivAt_id u).mul (h1.comp u h2)
    refine h3.congr_deriv ?_
    rw [cosSqrt_eq_sincSqrt_add]
    simp only [Function.comp_apply, one_mul, id_eq, add_right_inj]
    ring
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((contDiff_cosSqrt.continuous.comp (by fun_prop : Continuous fun u : ℝ => u ^ 2 *
      y)).intervalIntegrable _ _)
  simp at this
  exact this.symm

lemma iteratedDeriv_succ_cosSqrt (j : ℕ) :
    iteratedDeriv (j + 1) cosSqrt = fun y => -(1 / 2) * iteratedDeriv j sincSqrt y := by
  rw [iteratedDeriv_succ', deriv_cosSqrt]
  funext y
  exact iteratedDeriv_const_mul (-(1 / 2)) (contDiff_sincSqrt.contDiffAt.of_le le_top)

lemma contDiff_iteratedDeriv_cosSqrt (j : ℕ) : ContDiff ℝ 1 (iteratedDeriv j cosSqrt) := by
  rw [iteratedDeriv_eq_iterate]
  exact ((contDiff_cosSqrt.of_le le_top).iterate_deriv j).of_le (by exact_mod_cast le_top)

lemma iteratedDeriv_sincSqrt (j : ℕ) :
    iteratedDeriv j sincSqrt = fun y => ∫ u in (0:ℝ)..1, u ^ (2 * j) * iteratedDeriv j cosSqrt (u ^
      2 * y) := by
  induction j with
  | zero =>
    funext y
    simpa using sincSqrt_eq_integral y
  | succ j ih =>
    rw [iteratedDeriv_succ, ih]
    funext y
    have := hasDerivAt_integral_scale (contDiff_iteratedDeriv_cosSqrt j) (2 * j) y
    rw [this.deriv]
    refine intervalIntegral.integral_congr fun u _ => ?_
    simp only [iteratedDeriv_succ]
    ring_nf

/-- All derivatives of `cos √y` and `sinc √y` are bounded by `2⁻ʲ` on `[0, ∞)`. -/
lemma abs_iteratedDeriv_le (j : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    |iteratedDeriv j cosSqrt y| ≤ (1 / 2) ^ j ∧ |iteratedDeriv j sincSqrt y| ≤ (1 / 2) ^ j := by
  induction j generalizing y with
  | zero =>
    simp only [iteratedDeriv_zero, pow_zero]
    rw [cosSqrt_of_nonneg hy, sincSqrt_of_nonneg hy]
    exact ⟨abs_cos_le_one _, abs_sinc_le_one _⟩
  | succ j ih =>
    have hc : ∀ y' : ℝ, 0 ≤ y' → |iteratedDeriv (j + 1) cosSqrt y'| ≤ (1 / 2) ^ (j + 1) := by
      intro y' hy'
      rw [iteratedDeriv_succ_cosSqrt, abs_mul]
      have := (ih hy').2
      calc |-(1 / 2 : ℝ)| * |iteratedDeriv j sincSqrt y'| ≤ (1 / 2) * (1 / 2) ^ j := by
            rw [abs_neg, abs_of_pos (by norm_num : (0:ℝ) < 1 / 2)]
            gcongr
        _ = (1 / 2) ^ (j + 1) := by ring
    refine ⟨hc y hy, ?_⟩
    rw [iteratedDeriv_sincSqrt]
    have hb : ‖∫ u in (0:ℝ)..1, u ^ (2 * (j + 1)) * iteratedDeriv (j + 1) cosSqrt (u ^ 2 * y)‖
        ≤ (1 / 2) ^ (j + 1) * |(1:ℝ) - 0| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const fun u hu => ?_
      rw [uIoc_of_le zero_le_one] at hu
      have hu0 : 0 ≤ u := hu.1.le
      have hu1 : u ^ (2 * (j + 1)) ≤ 1 := pow_le_one₀ hu0 hu.2
      have := hc _ (mul_nonneg (sq_nonneg u) hy)
      rw [norm_mul, Real.norm_of_nonneg (pow_nonneg hu0 _), Real.norm_eq_abs]
      calc u ^ (2 * (j + 1)) * |iteratedDeriv (j + 1) cosSqrt (u ^ 2 * y)|
          ≤ 1 * (1 / 2) ^ (j + 1) := by gcongr
        _ = (1 / 2) ^ (j + 1) := one_mul _
    simpa [Real.norm_eq_abs] using hb

end Real
