/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Mathematics.Distribution.FourierMultiplier
public import PhyslibAlpha.Mathematics.SpecialFunctions.SincPropagator.Basic

/-!

# The propagation multiplier

The dispersion relation and the sine and cosine multipliers of the Klein–Gordon evolution.

## i. Overview

The dispersion relation and the sine and cosine multipliers of the Klein–Gordon evolution. They are
smooth and have temperate growth.

## ii. Key results

- `dispersion` : The dispersion `√((2π)² ‖ξ‖² + μ)` of the Klein–Gordon equation with mass parameter
  `μ`.
- `multiplier` : The Fourier multiplier of the propagation over the time `t`.
- `cosMultiplier` : The Fourier multiplier `cos (ω t)`.
- `frequencySq` : The Fourier multiplier `ω² = (2π)² ‖ξ‖² + μ`.

## iii. Table of contents

- A. The Klein–Gordon propagation multiplier
- B. The free Klein–Gordon evolution and its group law
- C. The propagation multiplier
- D. The homogeneous Klein–Gordon evolution of Schwartz data
- E. The retarded Klein–Gordon solution of a test-function source
- F. Smoothness of the retarded solution
- G. The retarded solution as a tempered distribution in space

## iv. References

None.

## A. The Klein–Gordon propagation multiplier

- `dispersion` : The dispersion `√((2π)² ‖ξ‖² + μ)` of the Klein–Gordon equation with mass parameter
  `μ`.
- `multiplier` : The Fourier multiplier of the propagation over the time `t`.

Lemmas: `dispersion_zero`, `norm_multiplier_le`, `multiplier_eq`,
`hasTemperateGrowth_comp_sincSqrt`, `hasTemperateGrowth_comp_cosSqrt`,
`hasTemperateGrowth_multiplier`.

## B. The free Klein–Gordon evolution and its group law

- `cosMultiplier` : The Fourier multiplier `cos (ω t)`.
- `frequencySq` : The Fourier multiplier `ω² = (2π)² ‖ξ‖² + μ`.

Lemmas: `cosMultiplier_eq`, `hasTemperateGrowth_cosMultiplier`, `hasTemperateGrowth_frequencySq`.

## C. The propagation multiplier

Lemmas: `continuous_dispersion`, `continuous_multiplier_uncurry`.

## D. The homogeneous Klein–Gordon evolution of Schwartz data

Lemmas: `continuous_cosMultiplier_uncurry`, `continuous_frequencySq`.

## E. The retarded Klein–Gordon solution of a test-function source

Lemmas: `dispersion_sq_le`.

## F. Smoothness of the retarded solution

Lemmas: `contDiff_multiplier_joint`.

## G. The retarded solution as a tempered distribution in space

Lemmas: `multiplier_neg`.

-/

@[expose] public section

noncomputable section

open scoped ContDiff Real
open FourierMultiplier Real Function Set TopologicalSpace Topology MeasureTheory
universe u

namespace KleinGordon

section
variable {E : Type*} [NormedAddCommGroup E]

/-- The dispersion `√((2π)² ‖ξ‖² + μ)` of the Klein–Gordon equation with mass parameter `μ`. -/
def dispersion (μ : ℝ) (ξ : E) : ℝ := √((2 * π) ^ 2 * ‖ξ‖ ^ 2 + μ)

/-- The massless dispersion is the norm of the frequency. -/
lemma dispersion_zero (ξ : E) : dispersion 0 ξ = 2 * Real.pi * ‖ξ‖ := by
  unfold dispersion
  rw [add_zero, show (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 = (2 * Real.pi * ‖ξ‖) ^ 2 by ring]
  exact Real.sqrt_sq (by positivity)

/-- The Fourier multiplier of the propagation over the time `t`. -/
def multiplier (t μ : ℝ) (ξ : E) : ℂ := (sincPropagator t (dispersion μ ξ) : ℂ)

lemma norm_multiplier_le (t μ : ℝ) (ξ : E) : ‖multiplier t μ ξ‖ ≤ |t| := by
  simpa [multiplier] using abs_sincPropagator_le t (dispersion μ ξ)

/-- For `μ ≥ 0` the multiplier is the entire function `t * sincSqrt` of `t² ω²`. -/
lemma multiplier_eq (t : ℝ) {μ : ℝ} (hμ : 0 ≤ μ) (ξ : E) :
    multiplier t μ ξ = ((t * sincSqrt (t ^ 2 * ((2 * π) ^ 2 * ‖ξ‖ ^ 2 + μ)) : ℝ) : ℂ) := by
  have h : 0 ≤ (2 * π) ^ 2 * ‖ξ‖ ^ 2 + μ := by positivity
  rw [multiplier, sincPropagator_eq_mul_sincSqrt, dispersion, Real.sq_sqrt h]
end

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma hasTemperateGrowth_comp_sincSqrt (t : ℝ) {q : E → ℝ} (hq : q.HasTemperateGrowth)
    (hq0 : ∀ ξ, 0 ≤ q ξ) : (fun ξ => t * sincSqrt (q ξ)).HasTemperateGrowth := by
  refine hasTemperateGrowth_comp_of_bounded (g := fun y => t * sincSqrt y)
    (contDiff_const.mul (contDiff_sincSqrt.of_le le_top)) (C := |t|) (fun n y hy => ?_) hq hq0
  rw [iteratedDeriv_const_mul_field, abs_mul]
  calc |t| * |iteratedDeriv n sincSqrt y| ≤ |t| * 1 := by
        gcongr
        exact (abs_iteratedDeriv_le n hy).2.trans (pow_le_one₀ (by norm_num) (by norm_num))
    _ = |t| := mul_one _

lemma hasTemperateGrowth_comp_cosSqrt {q : E → ℝ} (hq : q.HasTemperateGrowth)
    (hq0 : ∀ ξ, 0 ≤ q ξ) : (fun ξ => cosSqrt (q ξ)).HasTemperateGrowth :=
  hasTemperateGrowth_comp_of_bounded (contDiff_cosSqrt.of_le le_top) (C := 1)
    (fun n y hy => (abs_iteratedDeriv_le n hy).1.trans
      (pow_le_one₀ (by norm_num) (by norm_num))) hq hq0

/-- The propagation multiplier has temperate growth, also for `μ = 0`. -/
lemma hasTemperateGrowth_multiplier (t : ℝ) {μ : ℝ} (hμ : 0 ≤ μ) :
    (multiplier t μ : E → ℂ).HasTemperateGrowth := by
  have hq : (fun ξ : E => t ^ 2 * ((2 * π) ^ 2 * ‖ξ‖ ^ 2 + μ)).HasTemperateGrowth :=
    (HasTemperateGrowth.const _).mul
      (((HasTemperateGrowth.const _).mul (hasTemperateGrowth_norm_sq E)).add
        (HasTemperateGrowth.const _))
  have h := hasTemperateGrowth_comp_sincSqrt t hq (fun ξ => by positivity)
  have h2 := Complex.hasTemperateGrowth_ofReal.comp h
  convert h2 using 1
  funext ξ
  exact multiplier_eq t hμ ξ
end

section
variable {E : Type*} [NormedAddCommGroup E]

/-- The Fourier multiplier `cos (ω t)`. -/
def cosMultiplier (t μ : ℝ) (ξ : E) : ℂ := (cos (dispersion μ ξ * t) : ℝ)

/-- The Fourier multiplier `ω² = (2π)² ‖ξ‖² + μ`. -/
def frequencySq (μ : ℝ) (ξ : E) : ℂ := (((2 * π) ^ 2 * ‖ξ‖ ^ 2 + μ : ℝ) : ℂ)

lemma cosMultiplier_eq (t : ℝ) {μ : ℝ} (hμ : 0 ≤ μ) (ξ : E) :
    cosMultiplier t μ ξ = (cosSqrt (t ^ 2 * ((2 * π) ^ 2 * ‖ξ‖ ^ 2 + μ)) : ℝ) := by
  have h : 0 ≤ t ^ 2 * ((2 * π) ^ 2 * ‖ξ‖ ^ 2 + μ) := by positivity
  rw [cosSqrt_of_nonneg h, cosMultiplier]
  have : √(t ^ 2 * ((2 * π) ^ 2 * ‖ξ‖ ^ 2 + μ)) = |dispersion μ ξ * t| := by
    rw [Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq_eq_abs, abs_mul,
      abs_of_nonneg (by exact Real.sqrt_nonneg _ : 0 ≤ dispersion μ ξ), mul_comm]
    rfl
  rw [this, Real.cos_abs]
end

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (F : Type*) [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma hasTemperateGrowth_cosMultiplier (t : ℝ) {μ : ℝ} (hμ : 0 ≤ μ) :
    (cosMultiplier t μ : E → ℂ).HasTemperateGrowth := by
  have hq : (fun ξ : E => t ^ 2 * ((2 * π) ^ 2 * ‖ξ‖ ^ 2 + μ)).HasTemperateGrowth :=
    (Function.HasTemperateGrowth.const _).mul
      (((Function.HasTemperateGrowth.const _).mul (Function.hasTemperateGrowth_norm_sq E)).add
        (Function.HasTemperateGrowth.const _))
  have h := Complex.hasTemperateGrowth_ofReal.comp
    (hasTemperateGrowth_comp_cosSqrt hq (fun ξ => by positivity))
  convert h using 1
  funext ξ
  exact cosMultiplier_eq t hμ ξ

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma hasTemperateGrowth_frequencySq (μ : ℝ) :
    (frequencySq μ : E → ℂ).HasTemperateGrowth := by
  have h : (fun ξ : E => (2 * π) ^ 2 * ‖ξ‖ ^ 2 + μ).HasTemperateGrowth :=
    ((Function.HasTemperateGrowth.const _).mul (Function.hasTemperateGrowth_norm_sq E)).add
      (Function.HasTemperateGrowth.const _)
  exact Complex.hasTemperateGrowth_ofReal.comp h

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [NormedSpace
    ℂ F] [CompleteSpace F] in
lemma continuous_dispersion (μ : ℝ) : Continuous fun ξ : E => dispersion μ ξ := by
  unfold dispersion; fun_prop

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [NormedSpace
    ℂ F] [CompleteSpace F] in
lemma continuous_multiplier_uncurry (μ : ℝ) :
    Continuous fun p : ℝ × E => multiplier p.1 μ p.2 := by
  unfold multiplier
  exact Complex.continuous_ofReal.comp
    (continuous_sincPropagator.comp (continuous_fst.prodMk ((continuous_dispersion μ).comp
      continuous_snd)))
end

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]

omit [InnerProductSpace ℝ E] [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] in
lemma continuous_cosMultiplier_uncurry (μ : ℝ) :
    Continuous fun p : ℝ × E => cosMultiplier p.1 μ p.2 := by
  unfold cosMultiplier
  refine Complex.continuous_ofReal.comp (Real.continuous_cos.comp
    (((continuous_dispersion (E := E) μ).comp continuous_snd).mul continuous_fst))

omit [InnerProductSpace ℝ E] [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] in
lemma continuous_frequencySq : Continuous fun ξ : E => frequencySq (E := E) μ ξ := by
  unfold frequencySq; fun_prop

omit [InnerProductSpace ℝ E] [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] in
lemma dispersion_sq_le {μ : ℝ} (hμ : 0 ≤ μ) (ξ : E) :
    dispersion μ ξ ^ 2 ≤ ((2 * π) ^ 2 + μ) * (1 + ‖ξ‖) ^ 2 := by
  have h : 0 ≤ (2 * π) ^ 2 * ‖ξ‖ ^ 2 + μ := by positivity
  rw [dispersion, Real.sq_sqrt h]
  nlinarith [norm_nonneg ξ, sq_nonneg (2 * π), mul_nonneg hμ (norm_nonneg ξ)]
end

section
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] in
lemma contDiff_multiplier_joint {μ : ℝ} (hμ : 0 ≤ μ) :
    ContDiff ℝ ∞ fun z : ℝ × E => multiplier z.1 μ z.2 := by
  have e : (fun z : ℝ × E => multiplier z.1 μ z.2) = fun z =>
      (((z.1 * sincSqrt (z.1 ^ 2 * ((2 * π) ^ 2 * ‖z.2‖ ^ 2 + μ)) : ℝ)) : ℂ) :=
    funext fun z => multiplier_eq z.1 hμ z.2
  rw [e]
  have h1 : ContDiff ℝ ∞ fun z : ℝ × E => ‖z.2‖ ^ 2 := (contDiff_norm_sq ℝ).comp contDiff_snd
  have h2 : ContDiff ℝ ∞ fun z : ℝ × E => z.1 ^ 2 * ((2 * π) ^ 2 * ‖z.2‖ ^ 2 + μ) :=
    (contDiff_fst.pow 2).mul ((contDiff_const.mul h1).add contDiff_const)
  have h3 : ContDiff ℝ ∞ fun z : ℝ × E => z.1 * sincSqrt (z.1 ^ 2 * ((2 * π) ^ 2 * ‖z.2‖ ^ 2 +
    μ)) :=
    contDiff_fst.mul ((Real.contDiff_sincSqrt.of_le le_top).comp h2)
  exact Complex.ofRealCLM.contDiff.comp h3

omit [InnerProductSpace ℝ E] [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] in
lemma multiplier_neg (r μ : ℝ) (ξ : E) : multiplier r μ (-ξ) = multiplier r μ ξ := by
  simp [multiplier, dispersion]
end

end KleinGordon
