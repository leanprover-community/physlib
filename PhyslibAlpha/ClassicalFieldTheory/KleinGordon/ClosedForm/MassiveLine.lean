/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.KleinGordon.ClosedForm.MasslessLine
public import PhyslibAlpha.Mathematics.SpecialFunctions.SincPropagator.Bessel

/-!

# The retarded solution of the Klein–Gordon equation on the line

The retarded Green function in one space dimension is `½ Θ(t - |x|) J₀(m √(t² - x²))`.

## i. Overview

A multiplier that is the cosine transform of an even continuous kernel on `[-r, r]` is the
convolution with that kernel. The Bessel identity says that the multiplier of the massive sine
evolution is the cosine transform of `½ J₀(m √(r² - u²))`. So the sine evolution on the line is the
average of the data against the Bessel kernel over `[x - r, x + r]`. The Duhamel integral then gives
the retarded solution as the integral of the source against the retarded Green function over the
backward light cone. For `m = 0` this is the d'Alembert formula.

## ii. Key results

- `sineEvolution_of_kernel` : a cosine-transform multiplier is a convolution.
- `sineEvolution_mass_line` : the sine evolution with mass on the line.
- `solution_mass_line` : the retarded solution with mass on the line.

## iii. Table of contents

- A. Convolution kernels
- B. The Bessel kernel

## iv. References

None.

## A. Convolution kernels

- `sineEvolution_of_kernel` : a cosine-transform multiplier is a convolution.

## B. The Bessel kernel

- `sineEvolution_mass_line` : the sine evolution with mass on the line.
- `solution_mass_line` : the retarded solution with mass on the line.
-/

@[expose] public section

noncomputable section

open scoped FourierTransform SchwartzMap
open MeasureTheory

namespace KleinGordon

/-- **A multiplier that is a cosine transform is a convolution.** -/
lemma sineEvolution_of_kernel {μ r : ℝ} (hμ : 0 ≤ μ) (hr : 0 ≤ r) (w : ℝ → ℝ) (W : ℝ)
    (hw : Continuous w) (hwb : ∀ u, |w u| ≤ W) (hwe : ∀ u, w (-u) = w u)
    (hm : ∀ ξ : ℝ, multiplier r μ ξ =
      ((∫ u in (-r)..r, w u * Real.cos (2 * Real.pi * ξ * u) : ℝ) : ℂ))
    (g : 𝓢(ℝ, ℂ)) (x : ℝ) :
    sineEvolution ℂ r μ g x = ∫ u in (-r)..r, (w u : ℂ) * g (x + u) := by
  have hcos : ∀ (u ξ : ℝ), (Real.cos (2 * Real.pi * ξ * u) : ℂ) =
      (1 / 2 : ℂ) * ((𝐞 (u * ξ) : ℂ) + (𝐞 (-u * ξ) : ℂ)) := fun u ξ => by
    rw [Real.fourierChar_apply, Real.fourierChar_apply, Complex.ofReal_cos, Complex.cos]
    push_cast
    ring_nf
  have hmult : ∀ ξ : ℝ, multiplier r μ ξ =
      ∫ u in (-r)..r, (w u : ℂ) * (Real.cos (2 * Real.pi * ξ * u) : ℂ) := fun ξ => by
    rw [hm ξ, ← intervalIntegral.integral_ofReal]
    push_cast
    rfl
  have hrr : -r ≤ r := by linarith
  have key : ∀ u : ℝ, ∫ ξ : ℝ, (𝐞 (x * ξ) : ℂ) * ((w u : ℂ) * (Real.cos (2 * Real.pi * ξ * u) : ℂ)
      * 𝓕 g ξ) = (w u : ℂ) * (1 / 2 : ℂ) * (g (x + u) + g (x - u)) := fun u => by
    have h1 := SchwartzMap.integral_char_mul_fourier g (x + u)
    have h2 := SchwartzMap.integral_char_mul_fourier g (x - u)
    have : ∀ ξ : ℝ, (𝐞 (x * ξ) : ℂ) * ((w u : ℂ) * (Real.cos (2 * Real.pi * ξ * u) : ℂ)
        * 𝓕 g ξ) = (w u : ℂ) * (1 / 2 : ℂ) * ((𝐞 ((x + u) * ξ) : ℂ) * 𝓕 g ξ +
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
  have hF : ∀ ξ : ℝ, (𝐞 (x * ξ) : ℂ) * (multiplier r μ ξ * 𝓕 g ξ) =
      ∫ u in Set.Ioc (-r) r, (𝐞 (x * ξ) : ℂ) *
        ((w u : ℂ) * (Real.cos (2 * Real.pi * ξ * u) : ℂ) * 𝓕 g ξ) := fun ξ => by
    rw [hmult, intervalIntegral.integral_of_le hrr, ← integral_mul_const, ← integral_const_mul]
  have hcont : Continuous (Function.uncurry fun (ξ : ℝ) (u : ℝ) => (𝐞 (x * ξ) : ℂ) *
      ((w u : ℂ) * (Real.cos (2 * Real.pi * ξ * u) : ℂ) * 𝓕 g ξ)) := by
    have h1 : Continuous fun q : ℝ × ℝ => (𝐞 (x * q.1) : ℂ) :=
      continuous_subtype_val.comp (Real.continuous_fourierChar.comp
        (continuous_const.mul continuous_fst))
    have h2 : Continuous fun q : ℝ × ℝ => (Real.cos (2 * Real.pi * q.1 * q.2) : ℂ) :=
      Complex.continuous_ofReal.comp (Real.continuous_cos.comp
        ((continuous_const.mul continuous_fst).mul continuous_snd))
    have h3 : Continuous fun q : ℝ × ℝ => 𝓕 g q.1 := (𝓕 g).continuous.comp continuous_fst
    have h4 : Continuous fun q : ℝ × ℝ => (w q.2 : ℂ) :=
      Complex.continuous_ofReal.comp (hw.comp continuous_snd)
    exact h1.mul ((h4.mul h2).mul h3)
  have hint : Integrable (Function.uncurry fun (ξ : ℝ) (u : ℝ) => (𝐞 (x * ξ) : ℂ) *
      ((w u : ℂ) * (Real.cos (2 * Real.pi * ξ * u) : ℂ) * 𝓕 g ξ))
      (volume.prod (volume.restrict (Set.Ioc (-r) r))) := by
    have hb : Integrable (fun ξ : ℝ => W * ‖𝓕 g ξ‖) := (𝓕 g).integrable.norm.const_mul W
    have hc : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Set.Ioc (-r) r)) :=
      integrableOn_const (by simp)
    refine (hb.mul_prod hc).mono' hcont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun q => ?_)
    simp only [Function.uncurry, mul_one, norm_mul, Circle.norm_coe, one_mul]
    have hcos1 : ‖(Real.cos (2 * Real.pi * q.1 * q.2) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real]; exact Real.abs_cos_le_one _
    have hww : ‖(w q.2 : ℂ)‖ ≤ W := by rw [Complex.norm_real]; exact hwb q.2
    have hW0 : 0 ≤ W := (abs_nonneg _).trans (hwb 0)
    calc ‖(w q.2 : ℂ)‖ * ‖(Real.cos (2 * Real.pi * q.1 * q.2) : ℂ)‖ * ‖𝓕 g q.1‖
        ≤ W * 1 * ‖𝓕 g q.1‖ := by gcongr
      _ = _ := by ring
  rw [sineEvolution_apply_eq ℂ r hμ g x]
  have e : ∀ ξ : ℝ, (𝐞 (inner ℝ ξ x) : ℂ) • (multiplier r μ ξ • 𝓕 g ξ) =
      ∫ u in Set.Ioc (-r) r, (𝐞 (x * ξ) : ℂ) *
        ((w u : ℂ) * (Real.cos (2 * Real.pi * ξ * u) : ℂ) * 𝓕 g ξ) := fun ξ => by
    rw [← hF ξ]
    simp only [smul_eq_mul, RCLike.inner_apply, conj_trivial]
  calc ∫ ξ : ℝ, (𝐞 (inner ℝ ξ x) : ℂ) • (multiplier r μ ξ • 𝓕 g ξ)
      = ∫ ξ : ℝ, ∫ u in Set.Ioc (-r) r, (𝐞 (x * ξ) : ℂ) *
          ((w u : ℂ) * (Real.cos (2 * Real.pi * ξ * u) : ℂ) * 𝓕 g ξ) :=
        integral_congr_ae (Filter.Eventually.of_forall e)
    _ = ∫ u in Set.Ioc (-r) r, ∫ ξ : ℝ, (𝐞 (x * ξ) : ℂ) *
          ((w u : ℂ) * (Real.cos (2 * Real.pi * ξ * u) : ℂ) * 𝓕 g ξ) :=
        integral_integral_swap hint
    _ = ∫ u in Set.Ioc (-r) r, (w u : ℂ) * (1 / 2 : ℂ) * (g (x + u) + g (x - u)) :=
        setIntegral_congr_fun measurableSet_Ioc fun u _ => key u
    _ = ∫ u in (-r)..r, (w u : ℂ) * g (x + u) := by
        rw [← intervalIntegral.integral_of_le hrr]
        have i1 : IntervalIntegrable (fun u => (w u : ℂ) * g (x + u)) volume (-r) r :=
          ((Complex.continuous_ofReal.comp hw).mul
            (g.continuous.comp (continuous_const.add continuous_id))).intervalIntegrable _ _
        have i2 : IntervalIntegrable (fun u => (w u : ℂ) * g (x - u)) volume (-r) r :=
          ((Complex.continuous_ofReal.comp hw).mul
            (g.continuous.comp (continuous_const.sub continuous_id))).intervalIntegrable _ _
        have hneg : ∫ u in (-r)..r, (w u : ℂ) * g (x - u) =
            ∫ u in (-r)..r, (w u : ℂ) * g (x + u) := by
          have := intervalIntegral.integral_comp_neg (a := -r) (b := r)
            (fun u : ℝ => (w u : ℂ) * g (x - u))
          simp only [neg_neg, hwe, sub_neg_eq_add] at this
          exact this.symm
        have hsplit : ∀ u : ℝ, (w u : ℂ) * (1 / 2 : ℂ) * (g (x + u) + g (x - u)) =
            (1 / 2 : ℂ) * ((w u : ℂ) * g (x + u) + (w u : ℂ) * g (x - u)) := fun u => by ring
        simp_rw [hsplit]
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add i1 i2, hneg]
        ring

/-- **The massive sine evolution on the line.** The sine evolution of the mass `m` is the average
of the data against the Bessel kernel `½ J₀ (m √(r² - u²))` over the interval of radius `r`. -/
lemma sineEvolution_mass_line {r : ℝ} (hr : 0 ≤ r) (m : ℝ) (g : 𝓢(ℝ, ℂ)) (x : ℝ) :
    sineEvolution ℂ r (m ^ 2) g x =
      ∫ u in (-r)..r, ((1 / 2 * Real.besselSq (m ^ 2 * (r ^ 2 - u ^ 2)) : ℝ) : ℂ) * g (x + u) := by
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
  have hwb : ∀ u, |w u| ≤ |1 / 2 * C| := fun u => by
    have := hC _ (harg u)
    rw [Real.norm_eq_abs] at this
    simp only [hw]
    rw [abs_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (this.trans (le_abs_self C)) (abs_nonneg _)
  have hwe : ∀ u, w (-u) = w u := fun u => by simp [hw]
  have hmult : ∀ ξ : ℝ, multiplier r M ξ =
      ((∫ u in (-r)..r, w u * Real.cos (2 * Real.pi * ξ * u) : ℝ) : ℂ) := fun ξ => by
    have h1 : ∫ u in (-r)..r, w u * Real.cos (2 * Real.pi * ξ * u) =
        1 / 2 * ∫ u in (-r)..r, Real.besselSq (M * (r ^ 2 - u ^ 2)) *
          Real.cos (2 * Real.pi * ξ * u) := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun u hu => ?_
      rw [Set.uIcc_of_le (by linarith)] at hu
      have : u ^ 2 ≤ r ^ 2 := by nlinarith [hu.1, hu.2]
      simp only [hw, min_eq_left this]
      ring
    rw [h1, Real.integral_besselSq_cos hr (2 * Real.pi * ξ) M (by positivity)]
    unfold multiplier dispersion
    rw [show (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 + M = (2 * Real.pi * ξ) ^ 2 + M by
      rw [Real.norm_eq_abs, sq_abs]; ring]
    push_cast
    ring
  rw [sineEvolution_of_kernel hM0 hr w _ hwc hwb hwe hmult g x]
  refine intervalIntegral.integral_congr fun u hu => ?_
  rw [Set.uIcc_of_le (by linarith)] at hu
  have : u ^ 2 ≤ r ^ 2 := by nlinarith [hu.1, hu.2]
  simp only [hw, min_eq_left this]

open TopologicalSpace TimeSlice in
/-- **The retarded solution of the Klein–Gordon equation on the line.** The retarded solution at
`(t, x)` is the integral of the source against the retarded Green function
`½ Θ(t - s - |u|) J₀ (m √((t - s)² - u²))` over the backward light cone. -/
lemma solution_mass_line (m : ℝ) (ψ : TestFunction (⊤ : Opens (ℝ × ℝ)) ℂ ⊤) (t x : ℝ) :
    solution ℂ ψ (m ^ 2) t x = ∫ s in Set.Iic t, ∫ u in (-(t - s))..(t - s),
      ((1 / 2 * Real.besselSq (m ^ 2 * ((t - s) ^ 2 - u ^ 2)) : ℝ) : ℂ) * ψ (s, x + u) := by
  rw [solution_eq_integral ℂ ψ (sq_nonneg m) t x]
  refine setIntegral_congr_fun measurableSet_Iic fun s hs => ?_
  have hts : 0 ≤ t - s := sub_nonneg.2 hs
  exact sineEvolution_mass_line hts m (slice ℂ ψ s) x

end KleinGordon
