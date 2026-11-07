/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!

# Fourier inversion for Schwartz functions on the line

A Schwartz function on the line is the integral of its transform against the exponential.

## i. Overview

Mathlib states Fourier inversion for the Fourier multiplier on the Schwartz space. This file
unfolds it to the pointwise integral with the character `𝐞 (y * ξ)`. The integrand is integrable
because the transform is.

## ii. Key results

- `SchwartzMap.integral_char_smul_fourier` : the pointwise inversion formula.
- `SchwartzMap.integral_char_mul_fourier` : the same with the product in place of the scalar action.
- `SchwartzMap.integrable_char_mul_fourier` : the integrand is integrable.

## iii. Table of contents

- A. Pointwise inversion

## iv. References

None.

## A. Pointwise inversion

- `SchwartzMap.integral_char_smul_fourier` : the pointwise inversion formula.
- `SchwartzMap.integral_char_mul_fourier` : the same with the product.
- `SchwartzMap.integrable_char_mul_fourier` : the integrand is integrable.
-/

@[expose] public section

noncomputable section

open scoped FourierTransform SchwartzMap
open MeasureTheory

namespace SchwartzMap

/-- **Fourier inversion on the line.** -/
lemma integral_char_smul_fourier (g : 𝓢(ℝ, ℂ)) (y : ℝ) :
    ∫ ξ : ℝ, (𝐞 (y * ξ) : ℂ) • 𝓕 g ξ = g y := by
  have h := congrArg (fun g : 𝓢(ℝ, ℂ) => g y)
    (FourierTransform.fourierInv_fourier_eq (E := 𝓢(ℝ, ℂ)) (F := 𝓢(ℝ, ℂ)) g)
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq] at h
  simp only [Circle.smul_def] at h
  exact h

/-- Fourier inversion on the line with the product in place of the scalar action. -/
lemma integral_char_mul_fourier (g : 𝓢(ℝ, ℂ)) (y : ℝ) :
    ∫ ξ : ℝ, (𝐞 (y * ξ) : ℂ) * 𝓕 g ξ = g y := by
  simpa only [smul_eq_mul] using integral_char_smul_fourier g y

/-- The integrand of Fourier inversion is integrable. -/
lemma integrable_char_mul_fourier (g : 𝓢(ℝ, ℂ)) (y : ℝ) :
    Integrable fun ξ : ℝ => (𝐞 (y * ξ) : ℂ) * 𝓕 g ξ := by
  have hc : Continuous fun ξ : ℝ => (𝐞 (y * ξ) : ℂ) * 𝓕 g ξ :=
    (continuous_subtype_val.comp (Real.continuous_fourierChar.comp
      (continuous_const.mul continuous_id))).mul (𝓕 g).continuous
  refine (𝓕 g).integrable.norm.mono' hc.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ξ => ?_)
  rw [norm_mul, Circle.norm_coe, one_mul]

end SchwartzMap
