/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.KleinGordon.ClosedForm.MassiveLine
public import PhyslibAlpha.Mathematics.Calculus.SymmetricInterval
public import PhyslibAlpha.ClassicalFieldTheory.KleinGordon.DimensionRaising.RadialLift

/-!

# The retarded Green function with mass in three space dimensions

The retarded Green function in three space dimensions is
`δ(t - r) / (4π r) - m J₁(m √(t² - r²)) / (4π √(t² - r²)) Θ(t - r)`.

## i. Overview

Dimension raising turns the one-dimensional Green function `½ Θ J₀(m √(t² - x²))` into the
three-dimensional one by `-(1 / (2π r)) ∂ᵣ`. The derivative of the step gives the shell
`δ(t - r) / (4π r)`. The derivative of `J₀` gives the tail with `J₁`.

## ii. Key results

- `sineEvolution_origin_radialSource` : the Kirchhoff–Bessel formula for the sine evolution at
  the origin.
- `solution_origin_radialSource_space` : the Kirchhoff–Bessel formula for the retarded solution on
  `Space 3`.
- `solution_origin_radialSource_besselJ1` : the same formula with `J₁`.

## iii. Table of contents

- A. The formula at the origin

## iv. References

None.

## A. The formula at the origin

- `sineEvolution_origin_radialSource` : the Kirchhoff–Bessel formula for the sine evolution at
  the origin.
- `solution_origin_radialSource` : the formula for the retarded solution on Euclidean three-space.
- `solution_origin_radialSource_space` : the Kirchhoff–Bessel formula for the retarded solution on
  `Space 3`.
- `solution_origin_radialSource_besselJ1` : the same formula with `J₁`.
-/

@[expose] public section

noncomputable section

open scoped Distributions ContDiff
open MeasureTheory Set Filter Topology

namespace KleinGordon

section Origin

open TimeSlice

/-- **The Kirchhoff–Bessel formula for the sine evolution at the origin.** For a radial source with
the profile `Φ` the massive sine evolution at the origin is
`τ Φ(τ) + 2 m² ∫₀^τ u² κ(m² (τ² - u²)) Φ(u) du`, where `κ = -J₁(z) / (2z)` at `y = z²`. -/
lemma sineEvolution_origin_radialSource (m : ℝ) {τ : ℝ} (hτ : 0 ≤ τ)
    (P : 𝓓((⊤ : TopologicalSpace.Opens (ℝ × ℝ)), ℂ)) (s : ℝ) :
    sineEvolution ℂ τ (m ^ 2) (slice ℂ (radialSource Eucl3 (liftProfile P)) s) 0 =
      (τ : ℂ) * liftProfile P (s, τ ^ 2) + ((2 * m ^ 2 : ℝ) : ℂ) *
        ∫ u in (0 : ℝ)..τ, ((u ^ 2 * Real.besselSqDeriv (m ^ 2 * (τ ^ 2 - u ^ 2)) : ℝ) : ℂ) *
          liftProfile P (s, u ^ 2) := by
  set M : ℝ := m ^ 2 with hM
  set p : ℝ → ℂ := fun q => P (s, q) with hp
  have hpS : ContDiff ℝ ∞ p := P.contDiff.comp (contDiff_const.prodMk contDiff_id)
  have hpc : HasCompactSupport p := hasCompactSupport_slice ℂ P s
  set g' := slice ℂ (radialSource Eucl3 (liftProfile P)) s with hg'
  set gb := slice ℂ (radialSource ℝ P) s with hgb
  have hgb_apply : ∀ x : ℝ, gb x = p (x ^ 2) := fun x => by
    rw [hgb, slice_apply, radialSource_apply, Real.norm_eq_abs, sq_abs]
  have hg'_apply : ∀ z : Eucl3, g' z = liftProfile P (s, ‖z‖ ^ 2) := fun z => by
    rw [hg', slice_apply, radialSource_apply]
  have hrad : Function.IsRadial g' := fun z z' hzz => by
    rw [hg'_apply, hg'_apply]
    have h : ‖z‖ = ‖z'‖ := hzz
    rw [h]
  have hmarg : ∀ x : ℝ, gb x = ∫ y : EuclideanSpace ℝ (Fin 2), g' (WithLp.toLp 2 (x, y)) :=
    fun x => by
      have := radialSource_marginal ℝ Eucl3 (LinearIsometryEquiv.refl ℝ Eucl3) P s x
      rw [hgb, slice_apply]
      simpa [hg', slice_apply] using this
  set w : ℝ → ℝ := fun u => 1 / 2 * Real.besselSq (M * (τ ^ 2 - u ^ 2)) with hw
  have hwc : Continuous w := by
    simp only [hw]
    exact continuous_const.mul (Real.continuous_besselSq.comp (by fun_prop))
  have hwe : ∀ u, w (-u) = w u := fun u => by simp [hw]
  have hF : ∀ x : ℝ, sineEvolution ℂ τ M gb x = ∫ u in (-τ)..τ, (w u : ℂ) * gb (x + u) :=
    fun x => sineEvolution_mass_line hτ m gb x
  set U : ℝ → ℂ := fun ρ => sineEvolution ℂ τ M g' (WithLp.toLp 2 (ρ, 0)) with hU
  have hrais : ∀ ρ : ℝ, 0 < ρ → HasDerivAt (fun t : ℝ => ∫ u in (-τ)..τ, (w u : ℂ) * gb (t + u))
      (-(2 * Real.pi * ρ : ℝ) • U ρ) ρ := fun ρ hρ => by
    have h := hasDerivAt_sineEvolution_radial (E := ℝ) (sq_nonneg m) τ g' hrad gb hmarg
      (e := (1 : ℝ)) (by simp) hρ
    have e1 : (fun t : ℝ => sineEvolution ℂ τ (m ^ 2) gb (t • (1 : ℝ))) =
        fun t : ℝ => ∫ u in (-τ)..τ, (w u : ℂ) * gb (t + u) :=
      funext fun t => by rw [smul_eq_mul, mul_one]; exact hF t
    rw [e1] at h
    simpa [hU] using h
  have hdgb : ∀ x : ℝ, HasDerivAt gb ((2 * x : ℝ) • deriv p (x ^ 2)) x := fun x => by
    have h1 : HasDerivAt p (deriv p (x ^ 2)) (x ^ 2) :=
      (hpS.differentiable (by simp) (x ^ 2)).hasDerivAt
    have h2 : HasDerivAt (fun u : ℝ => u ^ 2) (2 * x) x := by simpa using hasDerivAt_pow 2 x
    have h3 : HasDerivAt (fun u : ℝ => p (u ^ 2)) ((2 * x) • deriv p (x ^ 2)) x :=
      HasDerivAt.scomp (g₁ := p) (h := fun u : ℝ => u ^ 2) x h1 h2
    have e : (gb : ℝ → ℂ) = fun u => p (u ^ 2) := funext hgb_apply
    rw [e]
    exact h3
  have hderivgb : ∀ x : ℝ, deriv gb x = (2 * x : ℝ) • deriv p (x ^ 2) := fun x => (hdgb x).deriv
  set h : ℝ → ℂ := fun x => ((-(1 / Real.pi) : ℝ) : ℂ) * x * deriv p (x ^ 2) with hh
  have hUH : ∀ ρ : ℝ, 0 < ρ → U ρ = (∫ u in (-τ)..τ, (w u : ℂ) * h (ρ + u)) / ρ := fun ρ hρ => by
    have h1 := (hrais ρ hρ).unique
      (SymmetricInterval.hasDerivAt_convolution hτ w hwc gb (gb.smooth 1) ρ)
    have h2 : ∫ u in (-τ)..τ, (w u : ℂ) * deriv gb (ρ + u) =
        (-(2 * Real.pi) : ℝ) • ∫ u in (-τ)..τ, (w u : ℂ) * h (ρ + u) := by
      rw [← intervalIntegral.integral_smul]
      refine intervalIntegral.integral_congr fun u _ => ?_
      simp only [hderivgb, hh, Complex.real_smul]
      have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      push_cast
      field_simp
    rw [h2, Complex.real_smul, Complex.real_smul] at h1
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hρ' : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
    push_cast at h1
    rw [eq_div_iff hρ']
    have h3 : ((2 * Real.pi : ℝ) : ℂ) * (U ρ * ρ - ∫ u in (-τ)..τ, (w u : ℂ) * h (ρ + u)) = 0 := by
      push_cast
      linear_combination -h1
    have h4 : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by
      push_cast
      exact mul_ne_zero two_ne_zero hpi
    exact sub_eq_zero.1 ((mul_eq_zero.1 h3).resolve_left h4)
  have hdp : ContDiff ℝ ∞ (deriv p) := (contDiff_infty_iff_deriv.1 hpS).2
  have hhc : ContDiff ℝ ∞ h := by
    simp only [hh]
    exact (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp contDiff_id)).mul
      (hdp.comp (contDiff_id.pow 2))
  have hhodd : ∀ x, h (-x) = -h x := fun x => by simp [hh]
  set H : ℝ → ℂ := fun ρ => ∫ u in (-τ)..τ, (w u : ℂ) * h (ρ + u) with hH
  have hH0 : H 0 = 0 := by
    simp only [hH, zero_add]
    have := intervalIntegral.integral_comp_neg (a := -τ) (b := τ)
      (fun u : ℝ => (w u : ℂ) * h u)
    simp only [neg_neg, hwe, hhodd, mul_neg, intervalIntegral.integral_neg] at this
    have h5 : (∫ u in (-τ)..τ, (w u : ℂ) * h u) = -∫ u in (-τ)..τ, (w u : ℂ) * h u := this.symm
    linear_combination (1 / 2 : ℂ) * h5
  have hHd := SymmetricInterval.hasDerivAt_convolution hτ w hwc h (hhc.of_le (by simp)) 0
  have hlim : Filter.Tendsto U (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∫ u in (-τ)..τ, (w u : ℂ) * deriv h (0 + u))) := by
    have hs := (hHd.tendsto_slope_zero.mono_left
      (nhdsWithin_mono 0 (fun x (hx : x ∈ Set.Ioi (0 : ℝ)) => ne_of_gt hx)))
    refine hs.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : 0 < t := ht
    have hH0' : ∫ u in (-τ)..τ, (w u : ℂ) * h u = 0 := by simpa [hH] using hH0
    simp only [zero_add, hH0', sub_zero, Complex.real_smul]
    rw [hUH t ht']
    simp only [Complex.ofReal_inv]
    ring
  have hUc : Filter.Tendsto U (nhdsWithin 0 (Set.Ioi 0)) (nhds (U 0)) := by
    have : Continuous U := by
      simp only [hU]
      exact (sineEvolution ℂ τ M g').continuous.comp (by fun_prop)
    exact this.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hU0 : U 0 = ∫ u in (-τ)..τ, (w u : ℂ) * deriv h (0 + u) :=
    tendsto_nhds_unique hUc hlim
  have hPhi : ∀ x : ℝ, h x = (x : ℂ) * liftProfile P (s, x ^ 2) := fun x => by
    rw [liftProfile_apply]
    simp only [hh, Complex.real_smul]
    ring
  have hwdr : ∀ x : ℝ, HasDerivAt w (-(M * x * Real.besselSqDeriv (M * (τ ^ 2 - x ^ 2)))) x :=
    fun x => by
      have h1 : HasDerivAt (fun x : ℝ => M * (τ ^ 2 - x ^ 2)) (M * (-(2 * x))) x := by
        have := ((hasDerivAt_pow 2 x).const_sub (τ ^ 2)).const_mul M
        simpa using this
      have h2 := (Real.hasDerivAt_besselSq (M * (τ ^ 2 - x ^ 2))).scomp x h1
      have h3 := h2.const_mul (1 / 2 : ℝ)
      have h4 : HasDerivAt w (1 / 2 * ((M * (-(2 * x))) • Real.besselSqDeriv
          (M * (τ ^ 2 - x ^ 2)))) x := h3
      convert h4 using 1
      simp only [smul_eq_mul]
      ring
  have hwd : ∀ x : ℝ, HasDerivAt (fun x => (w x : ℂ)) (((-(M * x * Real.besselSqDeriv
      (M * (τ ^ 2 - x ^ 2)))) : ℝ) : ℂ) x := fun x => (hwdr x).ofReal_comp
  have hdh : Continuous (deriv h) := hhc.continuous_deriv (by simp)
  have hΦc : Continuous fun x : ℝ => liftProfile P (s, x ^ 2) :=
    (liftProfile P).continuous.comp (by fun_prop)
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := -τ) (b := τ)
    (u := fun x => (w x : ℂ)) (u' := fun x => (((-(M * x * Real.besselSqDeriv
      (M * (τ ^ 2 - x ^ 2)))) : ℝ) : ℂ)) (v := h) (v' := deriv h)
    (fun x _ => hwd x) (fun x _ => (hhc.differentiable (by simp) x).hasDerivAt)
    (by
      refine Continuous.intervalIntegrable ?_ _ _
      exact Complex.continuous_ofReal.comp (by
        have := Real.continuous_besselSqDeriv.comp
          (by fun_prop : Continuous fun x : ℝ => M * (τ ^ 2 - x ^ 2))
        fun_prop))
    (hdh.intervalIntegrable _ _)
  set f : ℝ → ℂ := fun x => ((x ^ 2 * Real.besselSqDeriv (M * (τ ^ 2 - x ^ 2)) : ℝ) : ℂ) *
    liftProfile P (s, x ^ 2) with hf
  have hfc : Continuous f := by
    simp only [hf]
    refine (Complex.continuous_ofReal.comp ?_).mul hΦc
    exact (continuous_pow 2).mul (Real.continuous_besselSqDeriv.comp (by fun_prop))
  have hfe : ∀ x, f (-x) = f x := fun x => by simp [hf]
  have hbd : ∀ x : ℝ, w x = 1 / 2 → True := fun _ _ => trivial
  have hwτ : (w τ : ℂ) = 1 / 2 := by simp [hw]
  have hwτ' : (w (-τ) : ℂ) = 1 / 2 := by rw [hwe]; exact hwτ
  have hhτ : h τ = (τ : ℂ) * liftProfile P (s, τ ^ 2) := hPhi τ
  have hhτ' : h (-τ) = -((τ : ℂ) * liftProfile P (s, τ ^ 2)) := by
    rw [hPhi]; simp
  have hint : ∫ x in (-τ)..τ, (((-(M * x * Real.besselSqDeriv (M * (τ ^ 2 - x ^ 2)))) : ℝ) : ℂ) *
      h x = -((M : ℂ) * ∫ x in (-τ)..τ, f x) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun x _ => ?_
    simp only [hPhi, hf]
    push_cast
    ring
  have hU0' : U 0 = (τ : ℂ) * liftProfile P (s, τ ^ 2) + (M : ℂ) * ∫ x in (-τ)..τ, f x := by
    rw [hU0]
    simp only [zero_add]
    rw [hibp, hwτ, hwτ', hhτ, hhτ', hint]
    ring
  have h00 : sineEvolution ℂ τ M g' 0 = U 0 := rfl
  rw [h00, hU0', SymmetricInterval.integral_symm_even hfc hfe τ]
  simp only [hf]
  push_cast
  ring

/-- **The Kirchhoff–Bessel formula for the retarded solution at the origin.** For a radial source
`ψ'(s, x) = Q(s, ‖x‖²)` in three space dimensions the massive retarded solution at `(t, 0)` is
`∫_{s ≤ t} [τ Φ(τ) + 2 m² ∫₀^τ u² κ(m² (τ² - u²)) Φ(u) du] ds` with `τ = t - s`,
`Φ(u) = Q(s, u²)` and `κ(z²) = -J₁(z) / (2 z)`. -/
lemma solution_origin_radialSource (m : ℝ)
    (P : 𝓓((⊤ : TopologicalSpace.Opens (ℝ × ℝ)), ℂ)) (t : ℝ) :
    solution ℂ (radialSource Eucl3 (liftProfile P)) (m ^ 2) t 0 =
      ∫ s in Set.Iic t, ((((t - s : ℝ)) : ℂ) * liftProfile P (s, (t - s) ^ 2) +
        ((2 * m ^ 2 : ℝ) : ℂ) * ∫ u in (0 : ℝ)..(t - s),
          ((u ^ 2 * Real.besselSqDeriv (m ^ 2 * ((t - s) ^ 2 - u ^ 2)) : ℝ) : ℂ) *
            liftProfile P (s, u ^ 2)) := by
  rw [solution_eq_integral ℂ _ (sq_nonneg m) t 0]
  refine setIntegral_congr_fun measurableSet_Iic fun s hs => ?_
  exact sineEvolution_origin_radialSource m (sub_nonneg.2 hs) P s

/-- **The Kirchhoff–Bessel formula on `Space 3`.** -/
lemma solution_origin_radialSource_space (m : ℝ)
    (P : 𝓓((⊤ : TopologicalSpace.Opens (ℝ × ℝ)), ℂ)) (t : ℝ) :
    solution ℂ (radialSource (Space 3) (liftProfile P)) (m ^ 2) t 0 =
      ∫ s in Set.Iic t, ((((t - s : ℝ)) : ℂ) * liftProfile P (s, (t - s) ^ 2) +
        ((2 * m ^ 2 : ℝ) : ℂ) * ∫ u in (0 : ℝ)..(t - s),
          ((u ^ 2 * Real.besselSqDeriv (m ^ 2 * ((t - s) ^ 2 - u ^ 2)) : ℝ) : ℂ) *
            liftProfile P (s, u ^ 2)) := by
  rw [← transportSource_spaceThree, solution_transportSource (sq_nonneg m), map_zero,
    solution_origin_radialSource]

/-- **The Kirchhoff–Bessel formula with `J₁`.** For `m ≠ 0` the retarded solution at the origin of
a radial source is `∫_{s ≤ t} [τ Φ(τ) - m ∫₀^τ u² J₁(m √(τ² - u²)) / √(τ² - u²) Φ(u) du] ds`. -/
lemma solution_origin_radialSource_besselJ1 {m : ℝ} (hm : m ≠ 0)
    (P : 𝓓((⊤ : TopologicalSpace.Opens (ℝ × ℝ)), ℂ)) (t : ℝ) :
    solution ℂ (radialSource (Space 3) (liftProfile P)) (m ^ 2) t 0 =
      ∫ s in Set.Iic t, ((((t - s : ℝ)) : ℂ) * liftProfile P (s, (t - s) ^ 2) -
        (m : ℂ) * ∫ u in (0 : ℝ)..(t - s),
          ((u ^ 2 * (Real.besselJ1 (m * Real.sqrt ((t - s) ^ 2 - u ^ 2)) /
            Real.sqrt ((t - s) ^ 2 - u ^ 2)) : ℝ) : ℂ) * liftProfile P (s, u ^ 2)) := by
  rw [solution_origin_radialSource_space]
  refine setIntegral_congr_fun measurableSet_Iic fun s hs => ?_
  have hτ : 0 ≤ t - s := sub_nonneg.2 hs
  have key : ((2 * m ^ 2 : ℝ) : ℂ) * ∫ u in (0 : ℝ)..(t - s),
      ((u ^ 2 * Real.besselSqDeriv (m ^ 2 * ((t - s) ^ 2 - u ^ 2)) : ℝ) : ℂ) *
        liftProfile P (s, u ^ 2) = -((m : ℂ) * ∫ u in (0 : ℝ)..(t - s),
          ((u ^ 2 * (Real.besselJ1 (m * Real.sqrt ((t - s) ^ 2 - u ^ 2)) /
            Real.sqrt ((t - s) ^ 2 - u ^ 2)) : ℝ) : ℂ) * liftProfile P (s, u ^ 2)) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr_ae ?_
    have hne : ∀ᵐ u : ℝ, u ≠ t - s := by
      rw [ae_iff]
      simp
    filter_upwards [hne] with u hu hmem
    rw [Set.uIoc_of_le hτ] at hmem
    have hlt : |u| < t - s := by
      rw [abs_of_pos hmem.1]
      exact lt_of_le_of_ne hmem.2 hu
    have h0 := Real.mul_besselSqDeriv_eq_besselJ1 hm hlt (u ^ 2)
    have hc : ((2 * m ^ 2 * (u ^ 2 * Real.besselSqDeriv (m ^ 2 * ((t - s) ^ 2 - u ^ 2))) : ℝ) :
        ℂ) = ((-(m * (u ^ 2 * (Real.besselJ1 (m * Real.sqrt ((t - s) ^ 2 - u ^ 2)) /
          Real.sqrt ((t - s) ^ 2 - u ^ 2)))) : ℝ) : ℂ) := by rw [h0]
    push_cast at hc ⊢
    linear_combination (liftProfile P (s, u ^ 2)) * hc
  rw [key]
  ring

end Origin

end KleinGordon
