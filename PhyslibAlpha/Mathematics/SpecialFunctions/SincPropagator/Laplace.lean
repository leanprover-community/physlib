/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Mathematics.SpecialFunctions.SincPropagator.Basic
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!

# The Laplace transform of the sine propagation function

The transform of `t ↦ sin (ω t) / ω` over the positive half line is `1 / (ω² - z²)`.

## i. Overview

The retarded Green function of the oscillator is the sine propagation function on the positive
half line. Its Fourier transform in time exists for frequencies in the upper half plane. It
equals `1 / (ω² - z²)`. The value at `ω = 0` is the transform of the identity function.

## ii. Key results

- `integral_exp_mul_sincPropagator` : the transform for a nonzero frequency.
- `integral_exp_mul_sincPropagator_zero` : the transform for zero frequency.

## iii. Table of contents

- A. The transform

## iv. References

None.

## A. The transform

- `integral_exp_mul_sincPropagator` : the transform for a nonzero frequency.
-/

@[expose] public section

noncomputable section

open MeasureTheory Complex

namespace Real

/-- The Laplace transform of the sine propagation function for a nonzero frequency. -/
lemma integral_exp_mul_sincPropagator {ω : ℝ} (hω : ω ≠ 0) {z : ℂ} (hz : 0 < z.im) :
    ∫ t in Set.Ioi (0 : ℝ), Complex.exp (I * z * t) * (t.sincPropagator ω : ℂ) =
      1 / ((ω : ℂ) ^ 2 - z ^ 2) := by
  have hre : ∀ s : ℝ, (I * (z + s)).re < 0 := fun s => by simp [hz]
  have hre' : ∀ s : ℝ, (I * (z - s)).re < 0 := fun s => by simp [hz]
  have key : ∀ t : ℝ, Complex.exp (I * z * t) * (t.sincPropagator ω : ℂ) =
      (1 / (2 * I * ω)) * (Complex.exp (I * (z + ω) * t) -
        Complex.exp (I * (z - ω) * t)) := fun t => by
    rw [Real.sincPropagator_eq_sin_div hω]
    push_cast
    rw [Complex.sin, show I * (z + ω) * t = I * z * t + ω * t * I by ring,
      show I * (z - ω) * t = I * z * t - ω * t * I by ring, Complex.exp_add, Complex.exp_sub,
      show -((ω : ℂ) * t) * I = -((ω : ℂ) * t * I) by ring, Complex.exp_neg]
    have hω' : (ω : ℂ) ≠ 0 := by exact_mod_cast hω
    have ha := Complex.exp_ne_zero ((ω : ℂ) * t * I)
    field_simp
    ring_nf
    simp [Complex.I_sq]
  simp_rw [key]
  rw [integral_const_mul, integral_sub, integral_exp_mul_complex_Ioi (hre ω),
    integral_exp_mul_complex_Ioi (hre' ω)]
  · simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    have h1 : I * (z + ω) ≠ 0 := by
      intro h; have := hre ω; rw [h] at this; simp at this
    have h2 : I * (z - ω) ≠ 0 := by
      intro h; have := hre' ω; rw [h] at this; simp at this
    have hI : (2 * I * ω : ℂ) ≠ 0 := by simp [hω]
    have h3 : z + ω ≠ 0 := fun h => h1 (by rw [h, mul_zero])
    have h4 : z - ω ≠ 0 := fun h => h2 (by rw [h, mul_zero])
    have h5 : (ω : ℂ) ^ 2 - z ^ 2 ≠ 0 := by
      intro h
      have : (z + ω) * (z - ω) = 0 := by linear_combination -h
      rcases mul_eq_zero.mp this with h | h
      · exact h3 h
      · exact h4 h
    have hω' : (ω : ℂ) ≠ 0 := by exact_mod_cast hω
    field_simp
    ring_nf
    simp [Complex.I_sq]
  · exact integrableOn_exp_mul_complex_Ioi (hre ω) 0
  · exact integrableOn_exp_mul_complex_Ioi (hre' ω) 0

/-- The Laplace transform of the sine propagation function at zero frequency. -/
lemma integral_exp_mul_sincPropagator_zero {z : ℂ} (hz : 0 < z.im) :
    ∫ t in Set.Ioi (0 : ℝ), Complex.exp (I * z * t) * (t.sincPropagator 0 : ℂ) =
      1 / ((0 : ℂ) ^ 2 - z ^ 2) := by
  set c : ℂ := I * z with hcdef
  have hcre : c.re = -z.im := by simp [hcdef]
  have hc0 : c ≠ 0 := fun h => by
    have := hcre; rw [h] at this; simp at this; linarith
  have hb : 0 < -c.re := by rw [hcre]; linarith
  have hint : MeasureTheory.IntegrableOn
      (fun t : ℝ => Complex.exp (c * t) * (t : ℂ)) (Set.Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 1) (b := z.im)
      (by norm_num) one_pos hz
    refine (h.mono_set le_rfl).mono' ?_ ?_
    · exact (by fun_prop : Continuous fun t : ℝ =>
        Complex.exp (c * t) * (t : ℂ)).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      simp [Complex.norm_exp, hcre, abs_of_pos (Set.mem_Ioi.mp ht)]
      rw [mul_comm]
  have hF : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Complex.exp (c * t) * (t / c - 1 / c ^ 2))
      (Complex.exp (c * t) * t) t := fun t => by
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 t := (hasDerivAt_id t).ofReal_comp
    have h2 := (h1.const_mul c).cexp
    have h3 := h2.mul ((h1.div_const c).sub_const (1 / c ^ 2))
    convert h3 using 1
    field_simp
    ring
  have hlim : Filter.Tendsto (fun t : ℝ => Complex.exp (c * t) * (t / c - 1 / c ^ 2))
      Filter.atTop (nhds 0) := by
    have hbz : 0 < z.im := hz
    have hlin : Filter.Tendsto (fun t : ℝ => z.im * t) Filter.atTop Filter.atTop :=
      Filter.tendsto_id.const_mul_atTop hbz
    have h0 : Filter.Tendsto (fun t : ℝ => Complex.exp (c * t)) Filter.atTop (nhds 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have := Real.tendsto_exp_neg_atTop_nhds_zero.comp hlin
      refine this.congr fun t => ?_
      simp [Complex.norm_exp, hcre, mul_comm]
    have h1 : Filter.Tendsto (fun t : ℝ => (t : ℂ) * Complex.exp (c * t)) Filter.atTop
        (nhds 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have := (tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hlin
      have h2 := this.const_mul z.im⁻¹
      rw [mul_zero] at h2
      refine h2.congr' ?_
      filter_upwards [Filter.eventually_gt_atTop 0] with t ht
      simp only [Function.comp_apply, pow_one, norm_mul, Complex.norm_exp,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
      field_simp
      have hre : (c * (t : ℂ)).re = -(z.im * t) := by simp [hcre]
      rw [hre]
    have h3 := (h1.div_const c).sub (h0.div_const (c ^ 2))
    rw [zero_div, zero_div, sub_zero] at h3
    refine h3.congr fun t => ?_
    field_simp
  have := integral_Ioi_of_hasDerivAt_of_tendsto' (a := 0) (fun x _ => hF x) hint hlim
  simp_rw [Real.sincPropagator_zero_right]
  rw [show (fun t : ℝ => Complex.exp (I * z * t) * (t : ℂ)) =
    fun t : ℝ => Complex.exp (c * t) * (t : ℂ) from rfl, this]
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  simp only [hcdef, Complex.ofReal_zero, mul_zero, Complex.exp_zero, zero_div, zero_sub, one_mul]
  rw [mul_pow, Complex.I_sq]
  field_simp
  ring

/-- The Laplace transform of the sine propagation function for every frequency. -/
lemma integral_exp_mul_sincPropagator_all (ω : ℝ) {z : ℂ} (hz : 0 < z.im) :
    ∫ t in Set.Ioi (0 : ℝ), Complex.exp (I * z * t) * (t.sincPropagator ω : ℂ) =
      1 / ((ω : ℂ) ^ 2 - z ^ 2) := by
  by_cases hω : ω = 0
  · subst hω
    simpa using integral_exp_mul_sincPropagator_zero hz
  · exact integral_exp_mul_sincPropagator hω hz

end Real
