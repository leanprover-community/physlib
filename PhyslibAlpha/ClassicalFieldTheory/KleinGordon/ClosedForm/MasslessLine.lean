/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.KleinGordon.RetardedSolution
public import PhyslibAlpha.Mathematics.Fourier.Inversion
public import Mathlib.Analysis.Fourier.Inversion
public import PhyslibAlpha.Mathematics.Distribution.TimeSlice

/-!

# The retarded solution of the wave equation in one space dimension

The massless retarded solution in one space dimension is one half of the integral of the source
over the backward light cone.

## i. Overview

The multiplier `sin (2π |ξ| r) / (2π |ξ|)` of the massless sine evolution is the average of
`cos (2π ξ u)` over `u ∈ [-r, r]`. Fourier inversion turns it into the average of the data over the
interval `[x - r, x + r]`. The Duhamel integral over the earlier times is then the integral of the
source over the backward light cone. This is the retarded Green function `½ Θ(t - |x|)` of the wave
equation on the line. It is the case `d = 1` and `m = 0` of the explicit kernels.

## ii. Key results

- `multiplier_zero_eq` : the multiplier as an average of cosines.
- `sineEvolution_zero_mass_apply` : the massless sine evolution on the line is the average of the
  data over an interval.
- `solution_zero_mass_line` : the massless retarded solution on the line is one half of the
  integral of the source over the backward light cone.

## iii. Table of contents

- A. The multiplier
- B. The sine evolution
- C. The retarded solution

## iv. References

None.

## A. The multiplier

- `multiplier_zero_eq` : the multiplier as an average of cosines.

## B. The sine evolution

- `sineEvolution_zero_mass_apply` : the massless sine evolution on the line is the average of the
  data over an interval.

## C. The retarded solution

- `solution_zero_mass_line` : the massless retarded solution on the line is one half of the
  integral of the source over the backward light cone.
-/

@[expose] public section

noncomputable section

open scoped FourierTransform SchwartzMap
open MeasureTheory

namespace KleinGordon

/-- The massless multiplier on the line is the average of cosines over `[-r, r]`. -/
lemma multiplier_zero_eq (r : ℝ) (ξ : ℝ) :
    multiplier r 0 ξ = ((1 / 2 * ∫ u in (-r)..r, Real.cos (2 * Real.pi * ξ * u) : ℝ) : ℂ) := by
  have hd : dispersion (0 : ℝ) ξ = 2 * Real.pi * |ξ| := by
    unfold dispersion
    rw [add_zero, Real.norm_eq_abs, ← mul_pow, Real.sqrt_sq (by positivity)]
  unfold multiplier
  rw [hd]
  congr 1
  by_cases hξ : ξ = 0
  · subst hξ
    simp only [abs_zero, mul_zero, Real.sincPropagator_zero_right, zero_mul,
      Real.cos_zero, intervalIntegral.integral_const, smul_eq_mul]
    ring
  · have hc : 2 * Real.pi * ξ ≠ 0 := by positivity
    have hω : 2 * Real.pi * |ξ| ≠ 0 := by positivity
    rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x)
      (c := 2 * Real.pi * ξ) hc]
    simp only [integral_cos, smul_eq_mul]
    rw [Real.sincPropagator_eq_sin_div hω]
    rcases abs_cases ξ with ⟨h, -⟩ | ⟨h, -⟩
    · rw [h]
      rw [show 2 * Real.pi * ξ * -r = -(2 * Real.pi * ξ * r) by ring, Real.sin_neg]
      field_simp
      ring_nf
    · rw [h]
      rw [show 2 * Real.pi * ξ * -r = -(2 * Real.pi * ξ * r) by ring, Real.sin_neg]
      field_simp
      ring_nf
      rw [Real.sin_neg]
      ring

/-- **The massless sine evolution on the line.** The sine evolution at the origin of the
mass is the average of the data over the interval of radius `r`. -/
lemma sineEvolution_zero_mass_apply {r : ℝ} (hr : 0 ≤ r) (g : 𝓢(ℝ, ℂ)) (x : ℝ) :
    sineEvolution ℂ r 0 g x = 1 / 2 * ∫ y in (x - r)..(x + r), g y := by
  have hcos : ∀ (u ξ : ℝ), (Real.cos (2 * Real.pi * ξ * u) : ℂ) =
      (1 / 2 : ℂ) * ((𝐞 (u * ξ) : ℂ) + (𝐞 (-u * ξ) : ℂ)) := fun u ξ => by
    rw [Real.fourierChar_apply, Real.fourierChar_apply, Complex.ofReal_cos, Complex.cos]
    push_cast
    ring_nf
  have hmult : ∀ ξ : ℝ, multiplier r 0 ξ =
      ∫ u in (-r)..r, (1 / 2 : ℂ) * (Real.cos (2 * Real.pi * ξ * u) : ℂ) := fun ξ => by
    rw [multiplier_zero_eq, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_ofReal]
    push_cast
    ring
  have hrr : -r ≤ r := by linarith
  have key : ∀ u : ℝ, ∫ ξ : ℝ, (𝐞 (x * ξ) : ℂ) * ((1 / 2 : ℂ) * (Real.cos (2 * Real.pi * ξ * u) : ℂ)
      * 𝓕 g ξ) = (1 / 4 : ℂ) * (g (x + u) + g (x - u)) := fun u => by
    have h1 := SchwartzMap.integral_char_mul_fourier g (x + u)
    have h2 := SchwartzMap.integral_char_mul_fourier g (x - u)
    have : ∀ ξ : ℝ, (𝐞 (x * ξ) : ℂ) * ((1 / 2 : ℂ) * (Real.cos (2 * Real.pi * ξ * u) : ℂ)
        * 𝓕 g ξ) = (1 / 4 : ℂ) * ((𝐞 ((x + u) * ξ) : ℂ) * 𝓕 g ξ +
          (𝐞 ((x - u) * ξ) : ℂ) * 𝓕 g ξ) := fun ξ => by
      rw [hcos]
      have e1 : (𝐞 ((x + u) * ξ) : ℂ) = (𝐞 (x * ξ) : ℂ) * (𝐞 (u * ξ) : ℂ) := by
        rw [add_mul, Real.fourierChar_apply, Real.fourierChar_apply, Real.fourierChar_apply,
          ← Complex.exp_add]
        push_cast
        ring_nf
      have e2 : (𝐞 ((x - u) * ξ) : ℂ) = (𝐞 (x * ξ) : ℂ) * (𝐞 (-u * ξ) : ℂ) := by
        rw [show (x - u) * ξ = x * ξ + -u * ξ by ring, Real.fourierChar_apply,
          Real.fourierChar_apply, Real.fourierChar_apply, ← Complex.exp_add]
        push_cast
        ring_nf
      rw [e1, e2]
      ring
    simp_rw [this]
    rw [integral_const_mul, integral_add, h1, h2]
    · exact SchwartzMap.integrable_char_mul_fourier g _
    · exact SchwartzMap.integrable_char_mul_fourier g _
  have hF : ∀ ξ : ℝ, (𝐞 (x * ξ) : ℂ) * (multiplier r 0 ξ * 𝓕 g ξ) =
      ∫ u in Set.Ioc (-r) r, (𝐞 (x * ξ) : ℂ) *
        ((1 / 2 : ℂ) * (Real.cos (2 * Real.pi * ξ * u) : ℂ) * 𝓕 g ξ) := fun ξ => by
    rw [hmult, intervalIntegral.integral_of_le hrr, ← integral_mul_const, ← integral_const_mul]
  have hcont : Continuous (Function.uncurry fun (ξ : ℝ) (u : ℝ) => (𝐞 (x * ξ) : ℂ) *
      ((1 / 2 : ℂ) * (Real.cos (2 * Real.pi * ξ * u) : ℂ) * 𝓕 g ξ)) := by
    have h1 : Continuous fun q : ℝ × ℝ => (𝐞 (x * q.1) : ℂ) :=
      continuous_subtype_val.comp (Real.continuous_fourierChar.comp
        (continuous_const.mul continuous_fst))
    have h2 : Continuous fun q : ℝ × ℝ => (Real.cos (2 * Real.pi * q.1 * q.2) : ℂ) :=
      Complex.continuous_ofReal.comp (Real.continuous_cos.comp
        ((continuous_const.mul continuous_fst).mul continuous_snd))
    have h3 : Continuous fun q : ℝ × ℝ => 𝓕 g q.1 := (𝓕 g).continuous.comp continuous_fst
    exact h1.mul ((continuous_const.mul h2).mul h3)
  have hint : Integrable (Function.uncurry fun (ξ : ℝ) (u : ℝ) => (𝐞 (x * ξ) : ℂ) *
      ((1 / 2 : ℂ) * (Real.cos (2 * Real.pi * ξ * u) : ℂ) * 𝓕 g ξ))
      (volume.prod (volume.restrict (Set.Ioc (-r) r))) := by
    have hb : Integrable (fun ξ : ℝ => ‖𝓕 g ξ‖) := (𝓕 g).integrable.norm
    have hc : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Set.Ioc (-r) r)) :=
      integrableOn_const (by simp)
    refine (hb.mul_prod hc).mono' hcont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun q => ?_)
    simp only [Function.uncurry, mul_one, norm_mul, Circle.norm_coe, one_mul]
    have : ‖(Real.cos (2 * Real.pi * q.1 * q.2) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real]; exact Real.abs_cos_le_one _
    calc ‖(1 / 2 : ℂ)‖ * ‖(Real.cos (2 * Real.pi * q.1 * q.2) : ℂ)‖ * ‖𝓕 g q.1‖
        ≤ 1 * 1 * ‖𝓕 g q.1‖ := by gcongr; norm_num
      _ = _ := by ring
  rw [sineEvolution_apply_eq ℂ r le_rfl g x]
  have e : ∀ ξ : ℝ, (𝐞 (inner ℝ ξ x) : ℂ) • (multiplier r 0 ξ • 𝓕 g ξ) =
      ∫ u in Set.Ioc (-r) r, (𝐞 (x * ξ) : ℂ) *
        ((1 / 2 : ℂ) * (Real.cos (2 * Real.pi * ξ * u) : ℂ) * 𝓕 g ξ) := fun ξ => by
    rw [← hF ξ]
    simp only [smul_eq_mul, RCLike.inner_apply, conj_trivial]
  calc ∫ ξ : ℝ, (𝐞 (inner ℝ ξ x) : ℂ) • (multiplier r 0 ξ • 𝓕 g ξ)
      = ∫ ξ : ℝ, ∫ u in Set.Ioc (-r) r, (𝐞 (x * ξ) : ℂ) *
          ((1 / 2 : ℂ) * (Real.cos (2 * Real.pi * ξ * u) : ℂ) * 𝓕 g ξ) :=
        integral_congr_ae (Filter.Eventually.of_forall e)
    _ = ∫ u in Set.Ioc (-r) r, ∫ ξ : ℝ, (𝐞 (x * ξ) : ℂ) *
          ((1 / 2 : ℂ) * (Real.cos (2 * Real.pi * ξ * u) : ℂ) * 𝓕 g ξ) :=
        integral_integral_swap hint
    _ = ∫ u in Set.Ioc (-r) r, (1 / 4 : ℂ) * (g (x + u) + g (x - u)) :=
        setIntegral_congr_fun measurableSet_Ioc fun u _ => key u
    _ = 1 / 2 * ∫ y in (x - r)..(x + r), g y := by
        rw [← intervalIntegral.integral_of_le hrr, intervalIntegral.integral_const_mul]
        have i1 : IntervalIntegrable (fun u => g (x + u)) volume (-r) r :=
          (g.continuous.comp (continuous_const.add continuous_id)).intervalIntegrable _ _
        have i2 : IntervalIntegrable (fun u => g (x - u)) volume (-r) r :=
          (g.continuous.comp (continuous_const.sub continuous_id)).intervalIntegrable _ _
        rw [intervalIntegral.integral_add i1 i2,
          intervalIntegral.integral_comp_add_left (fun y => g y) x,
          intervalIntegral.integral_comp_sub_left (fun y => g y) x]
        simp only [sub_neg_eq_add]
        rw [show x + -r = x - r by ring]
        ring

open TopologicalSpace TimeSlice in
/-- **The retarded solution of the wave equation on the line.** The massless retarded solution
at `(t, x)` is one half of the integral of the source over the backward light cone. This is the
retarded Green function `½ Θ(t - |x|)`. -/
lemma solution_zero_mass_line (ψ : TestFunction (⊤ : Opens (ℝ × ℝ)) ℂ ⊤) (t x : ℝ) :
    solution ℂ ψ 0 t x =
      1 / 2 * ∫ s in Set.Iic t, ∫ y in (x - (t - s))..(x + (t - s)), ψ (s, y) := by
  rw [solution_eq_integral ℂ ψ le_rfl t x, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Iic fun s hs => ?_
  have hts : 0 ≤ t - s := sub_nonneg.2 hs
  rw [sineEvolution_zero_mass_apply hts]
  rfl

end KleinGordon
