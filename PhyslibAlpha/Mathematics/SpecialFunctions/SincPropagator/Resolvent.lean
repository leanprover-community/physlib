/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Mathematics.Fourier.Inversion
public import PhyslibAlpha.Mathematics.SpecialFunctions.SincPropagator.Laplace

/-!

# Resolvent estimates for the sine propagation function

The damped time integral of the sine propagation function is a resolvent in the frequency.

## i. Overview

The Laplace transform of the sine propagation function is `1 / (ω² - z²)`. Fourier inversion turns
the damped time integral against a Schwartz function into an integral over the frequency. The
resolvent `1 / (A - (b + i ε)²)` is bounded by `2 / ε²` for `A ≥ 0`. It is bounded by `2 / δ`
when `A` stays at distance `δ` from `b²`.

## ii. Key results

- `Real.integral_damped_sincPropagator` : the damped time integral as a frequency integral.
- `Real.norm_resolvent_le_two_div` : the bound `2 / ε²` for every nonnegative `A`.
- `Real.norm_resolvent_le` : the bound `2 / δ` away from the shell.

## iii. Table of contents

- A. Bounds of the resolvent
- B. The damped time integral

## iv. References

None.

## A. Bounds of the resolvent

- `Real.half_sq_le_norm_den` : the denominator is at least `ε² / 2`.
- `Real.norm_resolvent_le_two_div` : the bound `2 / ε²` for every nonnegative `A`.
- `Real.norm_resolvent_le` : the bound `2 / δ` away from the shell.

## B. The damped time integral

- `Real.integral_damped_sincPropagator` : the damped time integral as a frequency integral.
-/

@[expose] public section

noncomputable section

open scoped FourierTransform SchwartzMap
open MeasureTheory

namespace Real

/-- The denominator of the resolvent is bounded away from zero by `ε² / 2`. -/
lemma half_sq_le_norm_den {A : ℝ} (hA : 0 ≤ A) {ε : ℝ} (hε : 0 < ε) (b : ℝ) :
    ε ^ 2 / 2 ≤ ‖(A : ℂ) - (b + ε * Complex.I) ^ 2‖ := by
  have hre : ((A : ℂ) - (b + ε * Complex.I) ^ 2).re = A - b ^ 2 + ε ^ 2 := by
    simp [pow_two]
    ring
  have him : ((A : ℂ) - (b + ε * Complex.I) ^ 2).im = -(2 * b * ε) := by
    simp [pow_two]
    ring
  rcases le_or_gt (ε / 2) |b| with hb | hb
  · refine le_trans ?_ (Complex.abs_im_le_norm _)
    rw [him, abs_neg, abs_mul, abs_mul, abs_of_pos hε, abs_two]
    nlinarith
  · refine le_trans ?_ (Complex.abs_re_le_norm _)
    rw [hre]
    have : b ^ 2 < (ε / 2) ^ 2 := by
      rw [← sq_abs b]
      exact pow_lt_pow_left₀ hb (abs_nonneg b) two_ne_zero
    refine le_trans ?_ (le_abs_self _)
    nlinarith

/-- The resolvent is bounded by `2 / ε²` for every frequency. -/
lemma norm_resolvent_le_two_div {A : ℝ} (hA : 0 ≤ A) {ε : ℝ} (hε : 0 < ε) (b : ℝ) :
    ‖(1 : ℂ) / ((A : ℂ) - (b + ε * Complex.I) ^ 2)‖ ≤ 2 / ε ^ 2 := by
  have h1 := half_sq_le_norm_den hA hε b
  rw [norm_div, norm_one, div_le_div_iff₀ (lt_of_lt_of_le (by positivity) h1) (by positivity)]
  nlinarith

/-- The resolvent stays bounded away from the mass shell. -/
lemma norm_resolvent_le {A w ε δ : ℝ} (hδ : 0 < δ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hεδ : ε ≤ δ / 2) (h : δ ≤ |A - (2 * Real.pi * w) ^ 2|) :
    ‖(1 : ℂ) / ((A : ℂ) - (2 * Real.pi * w + ε * Complex.I) ^ 2)‖ ≤ 2 / δ := by
  have hre : ((A : ℂ) - (2 * Real.pi * w + ε * Complex.I) ^ 2).re =
      A - (2 * Real.pi * w) ^ 2 + ε ^ 2 := by
    simp [pow_two]
    ring
  have h1 : δ / 2 ≤ ‖(A : ℂ) - (2 * Real.pi * w + ε * Complex.I) ^ 2‖ := by
    refine le_trans ?_ (Complex.abs_re_le_norm _)
    rw [hre]
    have hεε : ε ^ 2 ≤ δ / 2 := by nlinarith
    have : δ - ε ^ 2 ≤ |A - (2 * Real.pi * w) ^ 2 + ε ^ 2| := by
      have := abs_sub_abs_le_abs_sub (A - (2 * Real.pi * w) ^ 2) (-ε ^ 2)
      rw [abs_neg, abs_of_nonneg (sq_nonneg ε)] at this
      have h2 : |A - (2 * Real.pi * w) ^ 2 - -ε ^ 2| = |A - (2 * Real.pi * w) ^ 2 + ε ^ 2| := by
        ring_nf
      linarith
    linarith
  rw [norm_div, norm_one]
  rw [div_le_div_iff₀ (lt_of_lt_of_le (by positivity) h1) hδ]
  nlinarith

/-- **Damped time integral.** The Fourier inversion and the Laplace transform of the sine
propagation function turn the damped time integral into an integral over the frequency. -/
lemma integral_damped_sincPropagator {ε : ℝ} (hε : 0 < ε) (w₀ : ℝ) (g : 𝓢(ℝ, ℂ)) :
    ∫ s in Set.Ioi (0 : ℝ), (Real.exp (-(ε * s)) : ℂ) * ((s.sincPropagator w₀ : ℂ) * g s) =
      ∫ w : ℝ, 𝓕 g w * (1 / ((w₀ : ℂ) ^ 2 - (2 * Real.pi * w + ε * Complex.I) ^ 2)) := by
  have hinv : ∀ s : ℝ, g s = ∫ w : ℝ, (𝐞 (s * w) : ℂ) • 𝓕 g w := fun s =>
    (SchwartzMap.integral_char_smul_fourier g s).symm
  let F : ℝ → ℝ → ℂ := fun s w =>
    (Real.exp (-(ε * s)) : ℂ) * ((s.sincPropagator w₀ : ℂ) * ((𝐞 (s * w) : ℂ) • 𝓕 g w))
  have hF : ∀ s : ℝ, (Real.exp (-(ε * s)) : ℂ) * ((s.sincPropagator w₀ : ℂ) * g s) =
      ∫ w : ℝ, F s w := fun s => by
    rw [hinv s, ← integral_const_mul, ← integral_const_mul]
  have hcont : Continuous (Function.uncurry F) := by
    have h1 : Continuous fun p : ℝ × ℝ => (p.1.sincPropagator w₀ : ℂ) :=
      Complex.continuous_ofReal.comp
        (Real.continuous_sincPropagator.comp (continuous_fst.prodMk continuous_const))
    have h2 : Continuous fun p : ℝ × ℝ => (𝐞 (p.1 * p.2) : ℂ) :=
      continuous_subtype_val.comp (Real.continuous_fourierChar.comp
        (continuous_fst.mul continuous_snd))
    have h3 : Continuous fun p : ℝ × ℝ => 𝓕 g p.2 := ((𝓕 g).continuous).comp continuous_snd
    have h4 : Continuous fun p : ℝ × ℝ => (Real.exp (-(ε * p.1)) : ℂ) :=
      Complex.continuous_ofReal.comp (Real.continuous_exp.comp
        (continuous_const.mul continuous_fst).neg)
    simp only [F]
    exact h4.mul (h1.mul (h2.mul h3))
  have hs : IntegrableOn (fun s : ℝ => s * Real.exp (-(ε * s))) (Set.Ioi 0) := by
    simpa using (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 1) (b := ε)
      (by norm_num) one_pos hε)
  have hint : Integrable (Function.uncurry F)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume) := by
    have hs' : IntegrableOn (fun s : ℝ => |s| * Real.exp (-(ε * s))) (Set.Ioi 0) :=
      hs.congr_fun (fun s hs => by rw [abs_of_pos hs]) measurableSet_Ioi
    refine ((hs'.mul_prod (𝓕 g).integrable.norm)).mono' hcont.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun z => ?_
    simp only [Function.uncurry, F, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [norm_smul, Circle.norm_coe, one_mul]
    have h1 := Real.abs_sincPropagator_le z.1 w₀
    have h2 := Real.exp_pos (-(ε * z.1))
    have h3 := norm_nonneg ((𝓕 g) z.2)
    calc Real.exp (-(ε * z.1)) * (|z.1.sincPropagator w₀| * ‖(𝓕 g) z.2‖)
        ≤ Real.exp (-(ε * z.1)) * (|z.1| * ‖(𝓕 g) z.2‖) := by gcongr
      _ = _ := by ring
  have hw : ∀ w : ℝ, ∫ s in Set.Ioi (0 : ℝ), F s w =
      𝓕 g w * (1 / ((w₀ : ℂ) ^ 2 - (2 * Real.pi * w + ε * Complex.I) ^ 2)) := fun w => by
    have hz : 0 < (2 * Real.pi * w + ε * Complex.I : ℂ).im := by simpa using hε
    have key : ∀ s : ℝ, F s w = 𝓕 g w * (Complex.exp (Complex.I *
        (2 * Real.pi * w + ε * Complex.I) * s) * (s.sincPropagator w₀ : ℂ)) := fun s => by
      have he : Complex.exp (Complex.I * (2 * Real.pi * w + ε * Complex.I) * s) =
          (Real.exp (-(ε * s)) : ℂ) * (𝐞 (s * w) : ℂ) := by
        rw [Real.fourierChar_apply, Complex.ofReal_exp, ← Complex.exp_add]
        congr 1
        push_cast
        ring_nf
        simp only [Complex.I_sq]
        ring
      simp only [F]
      rw [he]
      ring
    simp_rw [key]
    rw [integral_const_mul, Real.integral_exp_mul_sincPropagator_all w₀ hz]
  calc ∫ s in Set.Ioi (0 : ℝ), (Real.exp (-(ε * s)) : ℂ) * ((s.sincPropagator w₀ : ℂ) * g s)
      = ∫ s in Set.Ioi (0 : ℝ), ∫ w : ℝ, F s w :=
        setIntegral_congr_fun measurableSet_Ioi fun s _ => hF s
    _ = ∫ w : ℝ, ∫ s in Set.Ioi (0 : ℝ), F s w := integral_integral_swap hint
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall hw)

end Real
