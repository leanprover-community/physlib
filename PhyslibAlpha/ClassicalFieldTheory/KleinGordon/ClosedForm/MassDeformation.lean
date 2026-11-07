/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.KleinGordon.Solution
public import PhyslibAlpha.Mathematics.Calculus.SymmetricInterval
public import PhyslibAlpha.Mathematics.SpecialFunctions.SincPropagator.Bessel

/-!

# The massive sine evolution through the massless one

The massive sine evolution is the massless sine evolution plus a Bessel average of the massless
sine evolutions at smaller radii. This holds in every space dimension.

## i. Overview

The massive multiplier is a Bessel average of the massless cosine multipliers
(`Real.integral_besselSq_cos`). So the massive sine evolution is the Bessel average of the massless
cosine evolution. The massless cosine evolution is the derivative of the massless sine evolution.
Integration by parts moves the derivative to the Bessel weight.

## ii. Key results

- `cosineFourier` : the massless cosine evolution as a Fourier integral.
- `sineEvolution_mass_cos` : the massive sine evolution as a Bessel average of it.
- `hasDerivAt_sineEvolution_zero` : the cosine evolution is the derivative of the sine evolution.
- `sineEvolution_mass_zero` : the massive sine evolution through the massless one.

## iii. Table of contents

- A. The Bessel average of the cosine evolution
- B. The derivative of the sine evolution
- C. Integration by parts

## iv. References

None.

## A. The Bessel average of the cosine evolution

- `cosineFourier` : the massless cosine evolution as a Fourier integral.
- `sineEvolution_mass_cos` : the massive sine evolution as a Bessel average of it.

## B. The derivative of the sine evolution

- `hasDerivAt_sineEvolution_zero` : the cosine evolution is the derivative of the sine evolution.

## C. Integration by parts

- `sineEvolution_mass_zero` : the massive sine evolution through the massless one.
-/

@[expose] public section

noncomputable section

open scoped FourierTransform SchwartzMap
open MeasureTheory

namespace KleinGordon

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The cosine evolution of the massless wave equation, as a Fourier integral. -/
def cosineFourier (u : ℝ) (g : 𝓢(E, ℂ)) (x : E) : ℂ :=
  ∫ ξ : E, (𝐞 (inner ℝ ξ x) : ℂ) * ((Real.cos (2 * Real.pi * ‖ξ‖ * u) : ℂ) * 𝓕 g ξ)

/-- **The massive sine evolution is a Bessel average of the massless cosine evolution.** -/
lemma sineEvolution_mass_cos {r : ℝ} (hr : 0 ≤ r) (m : ℝ) (g : 𝓢(E, ℂ)) (x : E) :
    sineEvolution ℂ r (m ^ 2) g x =
      ∫ u in (-r)..r, ((1 / 2 * Real.besselSq (m ^ 2 * (r ^ 2 - u ^ 2)) : ℝ) : ℂ) *
        cosineFourier u g x := by
  set M : ℝ := m ^ 2 with hM
  have hM0 : 0 ≤ M := sq_nonneg m
  set w : ℝ → ℝ := fun u => 1 / 2 * Real.besselSq (M * (r ^ 2 - min (u ^ 2) (r ^ 2))) with hw
  have harg : ∀ u : ℝ, M * (r ^ 2 - min (u ^ 2) (r ^ 2)) ∈ Set.Icc (-(M * r ^ 2)) (M * r ^ 2) :=
    fun u => by
      have h1 : 0 ≤ min (u ^ 2) (r ^ 2) := le_min (sq_nonneg u) (sq_nonneg r)
      have h2 : min (u ^ 2) (r ^ 2) ≤ r ^ 2 := min_le_right _ _
      constructor <;> nlinarith [sq_nonneg r]
  have hwc : Continuous w := by
    have : Continuous fun u : ℝ => M * (r ^ 2 - min (u ^ 2) (r ^ 2)) := by fun_prop
    exact continuous_const.mul
      ((Real.continuousOn_besselSq (M * r ^ 2)).comp_continuous this harg)
  obtain ⟨C, hC⟩ :=
    (isCompact_Icc (a := -(M * r ^ 2)) (b := M * r ^ 2)).exists_bound_of_continuousOn
      (Real.continuousOn_besselSq (M * r ^ 2))
  set W : ℝ := |1 / 2 * C| with hW
  have hwb : ∀ u, |w u| ≤ W := fun u => by
    have := hC _ (harg u)
    rw [Real.norm_eq_abs] at this
    simp only [hw]
    rw [hW, abs_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (this.trans (le_abs_self C)) (abs_nonneg _)
  have hmult : ∀ ξ : E, multiplier r M ξ =
      ((∫ u in (-r)..r, w u * Real.cos (2 * Real.pi * ‖ξ‖ * u) : ℝ) : ℂ) := fun ξ => by
    have h1 : ∫ u in (-r)..r, w u * Real.cos (2 * Real.pi * ‖ξ‖ * u) =
        1 / 2 * ∫ u in (-r)..r, Real.besselSq (M * (r ^ 2 - u ^ 2)) *
          Real.cos (2 * Real.pi * ‖ξ‖ * u) := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun u hu => ?_
      rw [Set.uIcc_of_le (by linarith)] at hu
      have : u ^ 2 ≤ r ^ 2 := by nlinarith [hu.1, hu.2]
      simp only [hw, min_eq_left this]
      ring
    rw [h1, Real.integral_besselSq_cos hr (2 * Real.pi * ‖ξ‖) M (by positivity)]
    unfold multiplier dispersion
    rw [show (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 + M = (2 * Real.pi * ‖ξ‖) ^ 2 + M by ring]
    push_cast
    ring
  have hrr : -r ≤ r := by linarith
  have hmult' : ∀ ξ : E, multiplier r M ξ = ∫ u in (-r)..r,
      (w u : ℂ) * (Real.cos (2 * Real.pi * ‖ξ‖ * u) : ℂ) := fun ξ => by
    rw [hmult ξ, ← intervalIntegral.integral_ofReal]
    push_cast
    rfl
  have hF : ∀ ξ : E, (𝐞 (inner ℝ ξ x) : ℂ) * (multiplier r M ξ * 𝓕 g ξ) =
      ∫ u in Set.Ioc (-r) r, (𝐞 (inner ℝ ξ x) : ℂ) *
        ((w u : ℂ) * ((Real.cos (2 * Real.pi * ‖ξ‖ * u) : ℂ) * 𝓕 g ξ)) := fun ξ => by
    rw [hmult' ξ, intervalIntegral.integral_of_le hrr, ← integral_mul_const, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    ring
  have hcont : Continuous (Function.uncurry fun (ξ : E) (u : ℝ) =>
      (𝐞 (inner ℝ ξ x) : ℂ) *
        ((w u : ℂ) * ((Real.cos (2 * Real.pi * ‖ξ‖ * u) : ℂ) * 𝓕 g ξ))) := by
    have h1 : Continuous fun q : E × ℝ => (𝐞 (inner ℝ q.1 x) : ℂ) :=
      continuous_subtype_val.comp (Real.continuous_fourierChar.comp
        ((continuous_id.inner continuous_const).comp continuous_fst))
    have h2 : Continuous fun q : E × ℝ => (Real.cos (2 * Real.pi * ‖q.1‖ * q.2) : ℂ) :=
      Complex.continuous_ofReal.comp (Real.continuous_cos.comp
        ((continuous_const.mul (continuous_norm.comp continuous_fst)).mul continuous_snd))
    have h3 : Continuous fun q : E × ℝ => 𝓕 g q.1 := (𝓕 g).continuous.comp continuous_fst
    have h4 : Continuous fun q : E × ℝ => (w q.2 : ℂ) :=
      Complex.continuous_ofReal.comp (hwc.comp continuous_snd)
    exact h1.mul (h4.mul (h2.mul h3))
  have hint : Integrable (Function.uncurry fun (ξ : E) (u : ℝ) => (𝐞 (inner ℝ ξ x) : ℂ) *
      ((w u : ℂ) * ((Real.cos (2 * Real.pi * ‖ξ‖ * u) : ℂ) * 𝓕 g ξ)))
      (volume.prod (volume.restrict (Set.Ioc (-r) r))) := by
    have hb : Integrable (fun ξ : E => W * ‖𝓕 g ξ‖) := (𝓕 g).integrable.norm.const_mul W
    have hc : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Set.Ioc (-r) r)) :=
      integrableOn_const (by simp)
    refine (hb.mul_prod hc).mono' hcont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun q => ?_)
    simp only [Function.uncurry, mul_one, norm_mul, Circle.norm_coe, one_mul]
    have hcos1 : ‖(Real.cos (2 * Real.pi * ‖q.1‖ * q.2) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real]; exact Real.abs_cos_le_one _
    have hww : ‖(w q.2 : ℂ)‖ ≤ W := by rw [Complex.norm_real]; exact hwb q.2
    have hW0 : 0 ≤ W := (abs_nonneg _).trans (hwb 0)
    calc ‖(w q.2 : ℂ)‖ * (‖(Real.cos (2 * Real.pi * ‖q.1‖ * q.2) : ℂ)‖ * ‖𝓕 g q.1‖)
        ≤ W * (1 * ‖𝓕 g q.1‖) := by gcongr
      _ = _ := by ring
  rw [sineEvolution_apply_eq ℂ r hM0 g x]
  have e : ∀ ξ : E, (𝐞 (inner ℝ ξ x) : ℂ) • (multiplier r M ξ • 𝓕 g ξ) =
      ∫ u in Set.Ioc (-r) r, (𝐞 (inner ℝ ξ x) : ℂ) *
        ((w u : ℂ) * ((Real.cos (2 * Real.pi * ‖ξ‖ * u) : ℂ) * 𝓕 g ξ)) := fun ξ => by
    rw [← hF ξ]
    simp only [smul_eq_mul]
  calc ∫ ξ : E, (𝐞 (inner ℝ ξ x) : ℂ) • (multiplier r M ξ • 𝓕 g ξ)
      = ∫ ξ : E, ∫ u in Set.Ioc (-r) r, (𝐞 (inner ℝ ξ x) : ℂ) *
          ((w u : ℂ) * ((Real.cos (2 * Real.pi * ‖ξ‖ * u) : ℂ) * 𝓕 g ξ)) :=
        integral_congr_ae (Filter.Eventually.of_forall e)
    _ = ∫ u in Set.Ioc (-r) r, ∫ ξ : E, (𝐞 (inner ℝ ξ x) : ℂ) *
          ((w u : ℂ) * ((Real.cos (2 * Real.pi * ‖ξ‖ * u) : ℂ) * 𝓕 g ξ)) :=
        integral_integral_swap hint
    _ = ∫ u in Set.Ioc (-r) r, (w u : ℂ) * cosineFourier u g x := by
        refine setIntegral_congr_fun measurableSet_Ioc fun u _ => ?_
        unfold cosineFourier
        rw [← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
        ring
    _ = _ := by
        rw [← intervalIntegral.integral_of_le hrr]
        refine intervalIntegral.integral_congr fun u hu => ?_
        rw [Set.uIcc_of_le hrr] at hu
        have : u ^ 2 ≤ r ^ 2 := by nlinarith [hu.1, hu.2]
        simp only [hw, min_eq_left this]

/-- **The cosine evolution is the derivative of the sine evolution.** -/
lemma hasDerivAt_sineEvolution_zero (g : 𝓢(E, ℂ)) (x : E) (u₀ : ℝ) :
    HasDerivAt (fun u : ℝ => sineEvolution ℂ u 0 g x) (cosineFourier u₀ g x) u₀ := by
  set F : ℝ → E → ℂ := fun u ξ => (𝐞 (inner ℝ ξ x) : ℂ) * (multiplier u 0 ξ * 𝓕 g ξ) with hF
  set F' : ℝ → E → ℂ := fun u ξ =>
    (𝐞 (inner ℝ ξ x) : ℂ) * ((Real.cos (2 * Real.pi * ‖ξ‖ * u) : ℂ) * 𝓕 g ξ) with hF'
  have hfun : (fun u : ℝ => sineEvolution ℂ u 0 g x) = fun u => ∫ ξ : E, F u ξ := by
    funext u
    rw [sineEvolution_apply_eq ℂ u le_rfl g x]
    simp [hF, smul_eq_mul, Circle.smul_def]
  have hcF : ∀ u, Continuous (F u) := fun u => by
    simp only [hF, multiplier, dispersion_zero]
    have h1 : Continuous fun ξ : E => (𝐞 (inner ℝ ξ x) : ℂ) :=
      continuous_subtype_val.comp (Real.continuous_fourierChar.comp
        (continuous_id.inner continuous_const))
    have h2 : Continuous fun ξ : E => (Real.sincPropagator u (2 * Real.pi * ‖ξ‖) : ℂ) :=
      Complex.continuous_ofReal.comp (Real.continuous_sincPropagator.comp
        (continuous_const.prodMk (continuous_const.mul continuous_norm)))
    exact h1.mul (h2.mul (𝓕 g).continuous)
  have hcF' : ∀ u, Continuous (F' u) := fun u => by
    simp only [hF']
    have h1 : Continuous fun ξ : E => (𝐞 (inner ℝ ξ x) : ℂ) :=
      continuous_subtype_val.comp (Real.continuous_fourierChar.comp
        (continuous_id.inner continuous_const))
    have h2 : Continuous fun ξ : E => (Real.cos (2 * Real.pi * ‖ξ‖ * u) : ℂ) :=
      Complex.continuous_ofReal.comp (Real.continuous_cos.comp
        ((continuous_const.mul continuous_norm).mul continuous_const))
    exact h1.mul (h2.mul (𝓕 g).continuous)
  rw [hfun]
  have hn1 : ∀ ξ : E, ‖(𝐞 (inner ℝ ξ x) : ℂ)‖ = 1 := fun ξ => Circle.norm_coe _
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (x₀ := u₀)
    (F := F) (F' := F') (bound := fun ξ => ‖𝓕 g ξ‖) (s := Set.univ) Filter.univ_mem
    (Filter.Eventually.of_forall fun u => (hcF u).aestronglyMeasurable) ?_
    (hcF' u₀).aestronglyMeasurable ?_ (𝓕 g).integrable.norm ?_
  · exact key.2
  · refine ((𝓕 g).integrable.norm.const_mul |u₀|).mono' (hcF u₀).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ξ => ?_)
    simp only [hF, norm_mul, hn1, one_mul]
    calc ‖multiplier u₀ 0 ξ‖ * ‖𝓕 g ξ‖ ≤ |u₀| * ‖𝓕 g ξ‖ :=
          mul_le_mul_of_nonneg_right (norm_multiplier_le u₀ 0 ξ) (norm_nonneg _)
      _ = _ := rfl
  · refine Filter.Eventually.of_forall fun ξ u _ => ?_
    simp only [hF', norm_mul, hn1, one_mul]
    have : ‖(Real.cos (2 * Real.pi * ‖ξ‖ * u) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real]; exact Real.abs_cos_le_one _
    calc _ ≤ 1 * ‖𝓕 g ξ‖ := mul_le_mul_of_nonneg_right this (norm_nonneg _)
      _ = _ := one_mul _
  · refine Filter.Eventually.of_forall fun ξ u _ => ?_
    have h1 : HasDerivAt (fun u : ℝ => (Real.sincPropagator u (2 * Real.pi * ‖ξ‖) : ℝ))
        (Real.cos (2 * Real.pi * ‖ξ‖ * u)) u := Real.hasDerivAt_sincPropagator _ _
    have h2 := (h1.ofReal_comp).mul_const (𝓕 g ξ)
    have h3 := h2.const_mul (𝐞 (inner ℝ ξ x) : ℂ)
    simpa only [hF, hF', multiplier, dispersion_zero] using h3

lemma cosineFourier_neg (u : ℝ) (g : 𝓢(E, ℂ)) (x : E) :
    cosineFourier (-u) g x = cosineFourier u g x := by
  unfold cosineFourier
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [mul_neg, Real.cos_neg]

lemma continuous_cosineFourier (g : 𝓢(E, ℂ)) (x : E) : Continuous fun u => cosineFourier u g x := by
  unfold cosineFourier
  refine continuous_of_dominated (bound := fun ξ => ‖𝓕 g ξ‖) (fun u => ?_) (fun u => ?_)
    (𝓕 g).integrable.norm ?_
  · have h1 : Continuous fun ξ : E => (𝐞 (inner ℝ ξ x) : ℂ) :=
      continuous_subtype_val.comp (Real.continuous_fourierChar.comp
        (continuous_id.inner continuous_const))
    have h2 : Continuous fun ξ : E => (Real.cos (2 * Real.pi * ‖ξ‖ * u) : ℂ) :=
      Complex.continuous_ofReal.comp (Real.continuous_cos.comp
        ((continuous_const.mul continuous_norm).mul continuous_const))
    exact (h1.mul (h2.mul (𝓕 g).continuous)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun ξ => ?_
    simp only [norm_mul, Circle.norm_coe, one_mul]
    have : ‖(Real.cos (2 * Real.pi * ‖ξ‖ * u) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real]; exact Real.abs_cos_le_one _
    calc _ ≤ 1 * ‖𝓕 g ξ‖ := mul_le_mul_of_nonneg_right this (norm_nonneg _)
      _ = _ := one_mul _
  · refine Filter.Eventually.of_forall fun ξ => ?_
    have : Continuous fun u : ℝ => (Real.cos (2 * Real.pi * ‖ξ‖ * u) : ℂ) :=
      Complex.continuous_ofReal.comp (Real.continuous_cos.comp (continuous_const.mul continuous_id))
    exact continuous_const.mul (this.mul continuous_const)

/-- **The massive sine evolution in terms of the massless one.** The massive sine evolution is the
massless one at the radius plus a Bessel average of the massless sine evolution over smaller
radii. -/
lemma sineEvolution_mass_zero {r : ℝ} (hr : 0 ≤ r) (m : ℝ) (g : 𝓢(E, ℂ)) (x : E) :
    sineEvolution ℂ r (m ^ 2) g x = sineEvolution ℂ r 0 g x +
      ∫ u in (0 : ℝ)..r, ((2 * m ^ 2 * u * Real.besselSqDeriv (m ^ 2 * (r ^ 2 - u ^ 2)) : ℝ) : ℂ) *
        sineEvolution ℂ u 0 g x := by
  set M := m ^ 2 with hM
  set b : ℝ → ℝ := fun u => Real.besselSq (M * (r ^ 2 - u ^ 2)) with hb
  have hbd : ∀ u : ℝ, HasDerivAt b (-(2 * M * u * Real.besselSqDeriv (M * (r ^ 2 - u ^ 2)))) u :=
    fun u => by
      have h1 : HasDerivAt (fun u : ℝ => M * (r ^ 2 - u ^ 2)) (M * (-(2 * u))) u := by
        have := ((hasDerivAt_pow 2 u).const_sub (r ^ 2)).const_mul M
        convert this using 1
        simp
      have h2 := (Real.hasDerivAt_besselSq (M * (r ^ 2 - u ^ 2))).scomp u h1
      have h4 : HasDerivAt b ((M * -(2 * u)) • Real.besselSqDeriv (M * (r ^ 2 - u ^ 2))) u := h2
      convert h4 using 1
      rw [smul_eq_mul]
      ring
  have hbc : Continuous b := Real.continuous_besselSq.comp (by fun_prop)
  have hCc := continuous_cosineFourier g x
  have hCe : ∀ u, cosineFourier (-u) g x = cosineFourier u g x := fun u => cosineFourier_neg u g x
  have hmain := sineEvolution_mass_cos hr m g x
  have hfc : Continuous fun u : ℝ => ((1 / 2 * b u : ℝ) : ℂ) * cosineFourier u g x := by
    exact (Complex.continuous_ofReal.comp (continuous_const.mul hbc)).mul hCc
  have hfe : ∀ u : ℝ, ((1 / 2 * b (-u) : ℝ) : ℂ) * cosineFourier (-u) g x =
      ((1 / 2 * b u : ℝ) : ℂ) * cosineFourier u g x := fun u => by
    simp [hb, hCe]
  rw [hmain]
  change ∫ u in (-r)..r, ((1 / 2 * b u : ℝ) : ℂ) * cosineFourier u g x = _
  rw [SymmetricInterval.integral_symm_even hfc hfe r]
  have hWd : ∀ u : ℝ, HasDerivAt (fun u => sineEvolution ℂ u 0 g x) (cosineFourier u g x) u :=
    fun u => hasDerivAt_sineEvolution_zero g x u
  have hbdc : ∀ u : ℝ, HasDerivAt (fun u => (b u : ℂ))
      (((-(2 * M * u * Real.besselSqDeriv (M * (r ^ 2 - u ^ 2)))) : ℝ) : ℂ) u :=
    fun u => (hbd u).ofReal_comp
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := r)
    (u := fun u => (b u : ℂ)) (u' := fun u => (((-(2 * M * u *
      Real.besselSqDeriv (M * (r ^ 2 - u ^ 2)))) : ℝ) : ℂ))
    (v := fun u => sineEvolution ℂ u 0 g x) (v' := fun u => cosineFourier u g x)
    (fun u _ => hbdc u) (fun u _ => hWd u)
    (Continuous.intervalIntegrable (Complex.continuous_ofReal.comp (by
      have := Real.continuous_besselSqDeriv.comp
        (by fun_prop : Continuous fun u : ℝ => M * (r ^ 2 - u ^ 2))
      fun_prop)) _ _)
    (hCc.intervalIntegrable _ _)
  have hsum : ∀ u : ℝ, ((1 / 2 * b u : ℝ) : ℂ) * cosineFourier u g x =
      (1 / 2 : ℂ) * ((b u : ℂ) * cosineFourier u g x) := fun u => by push_cast; ring
  simp_rw [hsum]
  rw [intervalIntegral.integral_const_mul, hibp]
  have hb0 : b r = 1 := by simp [hb, Real.besselSq_zero]
  have hW0 : sineEvolution ℂ 0 0 g x = 0 := by
    simp [sineEvolution_zero]
  simp only [hb0, Complex.ofReal_one, one_mul, hW0, mul_zero, sub_zero]
  have hneg : ∀ u : ℝ, (((-(2 * M * u * Real.besselSqDeriv (M * (r ^ 2 - u ^ 2)))) : ℝ) : ℂ) *
      sineEvolution ℂ u 0 g x = -(((2 * M * u * Real.besselSqDeriv (M * (r ^ 2 - u ^ 2)) : ℝ) : ℂ) *
      sineEvolution ℂ u 0 g x) := fun u => by push_cast; ring
  simp_rw [hneg]
  rw [intervalIntegral.integral_neg]
  ring

end KleinGordon
