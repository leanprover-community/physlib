/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.KleinGordon.Multiplier

/-!

# The free evolution

## i. Overview

The sine and cosine evolution of Schwartz data and its time and space derivatives.

## ii. Key results

- `sineEvolution` : The propagation over the time `t` on Schwartz functions.
- `sineEvolutionTempered` : The propagation over the time `t` on tempered distributions.
- `cosEvolution` : The cosine evolution on Schwartz functions.
- `frequencySqOperator` : The Fourier multiplier `ω²`, i.e.
- `evolveU` : The field `u τ = C τ a + S τ b` evolved from the Cauchy data `(a, b)`.
- `evolveV` : The velocity `v τ = C τ b - ω² S τ a` of the evolved field.

## iii. Table of contents

- A. The Klein–Gordon propagation multiplier
- B. The free Klein–Gordon evolution and its group law
- C. The free evolution
- D. The free Klein–Gordon evolution as a one-parameter group
- E. The homogeneous Klein–Gordon evolution of Schwartz data

## iv. References

None.

## A. The Klein–Gordon propagation multiplier

- `sineEvolution` : The propagation over the time `t` on Schwartz functions.
- `sineEvolutionTempered` : The propagation over the time `t` on tempered distributions.

Lemmas: `sineEvolutionTempered_coe`.

## B. The free Klein–Gordon evolution and its group law

- `cosEvolution` : The cosine evolution on Schwartz functions.
- `frequencySqOperator` : The Fourier multiplier `ω²`, i.e.

## C. The free evolution

Lemmas: `sineEvolution_apply_eq`.

## D. The free Klein–Gordon evolution as a one-parameter group

Lemmas: `sineEvolution_zero`, `cosEvolution_zero`.

## E. The homogeneous Klein–Gordon evolution of Schwartz data

- `evolveU` : The field `u τ = C τ a + S τ b` evolved from the Cauchy data `(a, b)`.
- `evolveV` : The velocity `v τ = C τ b - ω² S τ a` of the evolved field.

Lemmas: `hasDerivAt_sineEvolution_apply`, `hasDerivAt_cosEvolution_apply`, `hasDerivAt_evolveU`,
`frequencySqOperator_sineEvolution`, `frequencySqOperator_cosEvolution`, `hasDerivAt_evolveV`,
`lineDeriv_evolveU`, `lineDeriv_evolveV`, `frequencySqOperator_eq`,
`continuous_sineEvolution_apply'` and more.

-/

@[expose] public section

noncomputable section

open scoped SchwartzMap FourierTransform ContDiff
open FourierMultiplier Real TopologicalSpace Topology

namespace KleinGordon

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (F : Type*) [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The propagation over the time `t` on Schwartz functions. -/
def sineEvolution (t μ : ℝ) : 𝓢(E, F) →L[ℂ] 𝓢(E, F) :=
  SchwartzMap.fourierMultiplierCLM F (multiplier t μ : E → ℂ)

/-- The propagation over the time `t` on tempered distributions. -/
def sineEvolutionTempered (t μ : ℝ) : 𝓢'(E, F) →L[ℂ] 𝓢'(E, F) :=
  TemperedDistribution.fourierMultiplierCLM F (multiplier t μ : E → ℂ)

/-- The two propagations agree on Schwartz functions. -/
lemma sineEvolutionTempered_coe [CompleteSpace F] (t : ℝ) {μ : ℝ} (hμ : 0 ≤ μ) (f : 𝓢(E, F)) :
    sineEvolutionTempered F t μ (f : 𝓢'(E, F)) = (sineEvolution F t μ f : 𝓢'(E, F)) :=
  TemperedDistribution.fourierMultiplierCLM_toTemperedDistributionCLM_eq
    (hasTemperateGrowth_multiplier t hμ) f
end

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (F : Type*) [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F]

/-- The cosine evolution on Schwartz functions. -/
def cosEvolution (t μ : ℝ) : 𝓢(E, F) →L[ℂ] 𝓢(E, F) :=
  SchwartzMap.fourierMultiplierCLM F (cosMultiplier t μ : E → ℂ)

/-- The Fourier multiplier `ω²`, i.e. `-Δ + μ`, on Schwartz functions. -/
def frequencySqOperator (μ : ℝ) : 𝓢(E, F) →L[ℂ] 𝓢(E, F) :=
  SchwartzMap.fourierMultiplierCLM F (frequencySq μ : E → ℂ)

omit [CompleteSpace F] in
/-- The pointwise Fourier integral of the sine evolution. -/
lemma sineEvolution_apply_eq (r : ℝ) {μ : ℝ} (hμ : 0 ≤ μ) (g : 𝓢(E, F)) (x : E) :
    sineEvolution F r μ g x = ∫ ξ : E, 𝐞 (inner ℝ ξ x) • (multiplier r μ ξ • 𝓕 g ξ) := by
  simp only [sineEvolution, SchwartzMap.fourierMultiplierCLM_apply]
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq]
  simp [SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_multiplier r hμ)]

lemma sineEvolution_zero (μ : ℝ) : sineEvolution (E := E) F 0 μ = 0 := by
  have : (multiplier 0 μ : E → ℂ) = fun _ => 0 := by
    funext ξ; simp [multiplier]
  rw [sineEvolution, this, SchwartzMap.fourierMultiplierCLM_const]
  simp

lemma cosEvolution_zero (μ : ℝ) : cosEvolution (E := E) F 0 μ = ContinuousLinearMap.id ℂ _ := by
  have : (cosMultiplier 0 μ : E → ℂ) = fun _ => 1 := by
    funext ξ; simp [cosMultiplier]
  rw [cosEvolution, this, SchwartzMap.fourierMultiplierCLM_const]
  simp
end

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F]

omit [CompleteSpace F] in
/-- The time derivative of the sine evolution of Schwartz data is the cosine evolution. -/
lemma hasDerivAt_sineEvolution_apply {μ : ℝ} (hμ : 0 ≤ μ) (b : 𝓢(E, F)) (x : E) (τ : ℝ) :
    HasDerivAt (fun r => sineEvolution F r μ b x) (cosEvolution F τ μ b x) τ := by
  refine hasDerivAt_multiplierFamily b x (fun r => multiplier r μ)
    (fun r => cosMultiplier r μ) (fun r => hasTemperateGrowth_multiplier r hμ)
    (fun r => hasTemperateGrowth_cosMultiplier r hμ) (fun ξ r => ?_) τ
    (fun ξ => ‖𝓕 b ξ‖) (𝓕 b).integrable.norm (fun ξ r _ => ?_)
  · have := (hasDerivAt_sincPropagator (dispersion μ ξ) r).ofReal_comp
    exact this
  · have : ‖cosMultiplier r μ ξ‖ ≤ 1 := by
      rw [cosMultiplier, Complex.norm_real, Real.norm_eq_abs]; exact abs_cos_le_one _
    calc ‖cosMultiplier r μ ξ‖ * ‖𝓕 b ξ‖ ≤ 1 * ‖𝓕 b ξ‖ :=
          mul_le_mul_of_nonneg_right this (norm_nonneg _)
      _ = _ := one_mul _

/-- The time derivative of the cosine evolution of Schwartz data. -/
lemma hasDerivAt_cosEvolution_apply {μ : ℝ} (hμ : 0 ≤ μ) (a : 𝓢(E, F)) (x : E) (τ : ℝ) :
    HasDerivAt (fun r => cosEvolution F r μ a x)
      (-(frequencySqOperator F μ (sineEvolution F τ μ a) x)) τ := by
  have hw := hasTemperateGrowth_frequencySq (E := E) μ
  have hcomp : ∀ r, frequencySqOperator F μ (sineEvolution F r μ a) =
      SchwartzMap.fourierMultiplierCLM F (frequencySq μ * multiplier r μ) a := fun r =>
    SchwartzMap.fourierMultiplierCLM_fourierMultiplierCLM_apply hw
      (hasTemperateGrowth_multiplier r hμ) a
  have hneg : ∀ r, SchwartzMap.fourierMultiplierCLM F (-(frequencySq μ * multiplier r μ)) a x =
      -(frequencySqOperator F μ (sineEvolution F r μ a) x) := by
    intro r
    rw [hcomp]
    have := congrArg (fun T => T a x) (SchwartzMap.fourierMultiplierCLM_smul (𝕜 := ℂ) (F := F)
      ((hw.mul (hasTemperateGrowth_multiplier r hμ))) (-1))
    simpa using this
  rw [← hneg τ]
  refine hasDerivAt_multiplierFamily a x (fun r => cosMultiplier r μ)
    (fun r => -(frequencySq μ * multiplier r μ)) (fun r => hasTemperateGrowth_cosMultiplier r hμ)
    (fun r => (hw.mul (hasTemperateGrowth_multiplier r hμ)).neg) (fun ξ r => ?_) τ
    (fun ξ => (|τ| + 1) * (((2 * π) ^ 2 * ‖ξ‖ ^ 2 + μ) * ‖𝓕 a ξ‖)) ?_ (fun ξ r hr => ?_)
  · have hω : dispersion μ ξ ^ 2 = (2 * π) ^ 2 * ‖ξ‖ ^ 2 + μ := Real.sq_sqrt (by positivity)
    have := (hasDerivAt_cos_mul (dispersion μ ξ) r).ofReal_comp
    convert this using 1
    · funext r'; rfl
    · simp only [Pi.neg_apply, Pi.mul_apply, frequencySq, multiplier]
      rw [← hω]
      push_cast
      ring
  · have h0 := ((𝓕 a).integrable (μ := MeasureTheory.volume)).norm
    have h2 : MeasureTheory.Integrable (fun ξ : E => ‖ξ‖ ^ 2 * ‖𝓕 a ξ‖) MeasureTheory.volume :=
      SchwartzMap.integrable_pow_mul MeasureTheory.volume (𝓕 a) 2
    convert ((h2.const_mul ((2 * π) ^ 2)).add (h0.const_mul μ)).const_mul (|τ| + 1) using 2 with ξ
    simp only [Pi.add_apply]
    ring
  · have hfs : ‖frequencySq μ ξ‖ = (2 * π) ^ 2 * ‖ξ‖ ^ 2 + μ := by
      rw [frequencySq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hm : ‖multiplier r μ ξ‖ ≤ |τ| + 1 := by
      refine (norm_multiplier_le r μ ξ).trans ?_
      have := Metric.mem_ball.1 hr
      rw [Real.dist_eq] at this
      calc |r| = |(r - τ) + τ| := by ring_nf
        _ ≤ |r - τ| + |τ| := abs_add_le _ _
        _ ≤ _ := by linarith
    simp only [Pi.neg_apply, Pi.mul_apply, norm_neg, norm_mul, hfs]
    calc ((2 * π) ^ 2 * ‖ξ‖ ^ 2 + μ) * ‖multiplier r μ ξ‖ * ‖𝓕 a ξ‖
        ≤ ((2 * π) ^ 2 * ‖ξ‖ ^ 2 + μ) * (|τ| + 1) * ‖𝓕 a ξ‖ := by gcongr
      _ = _ := by ring

/-- The field `u τ = C τ a + S τ b` evolved from the Cauchy data `(a, b)`. -/
def evolveU (μ τ : ℝ) (a b : 𝓢(E, F)) : 𝓢(E, F) :=
  cosEvolution F τ μ a + sineEvolution F τ μ b

/-- The velocity `v τ = C τ b - ω² S τ a` of the evolved field. -/
def evolveV (μ τ : ℝ) (a b : 𝓢(E, F)) : 𝓢(E, F) :=
  cosEvolution F τ μ b - frequencySqOperator F μ (sineEvolution F τ μ a)

lemma hasDerivAt_evolveU {μ : ℝ} (hμ : 0 ≤ μ) (a b : 𝓢(E, F)) (x : E) (τ : ℝ) :
    HasDerivAt (fun r => evolveU μ r a b x) (evolveV μ τ a b x) τ := by
  have h := (hasDerivAt_cosEvolution_apply hμ a x τ).add (hasDerivAt_sineEvolution_apply hμ b x τ)
  unfold evolveU evolveV
  simp only [add_apply, sub_apply]
  convert h using 1
  abel

lemma frequencySqOperator_sineEvolution {μ : ℝ} (hμ : 0 ≤ μ) (r : ℝ) (a : 𝓢(E, F)) :
    frequencySqOperator F μ (sineEvolution F r μ a) =
      sineEvolution F r μ (frequencySqOperator F μ a) :=
  multiplier_comm F (hasTemperateGrowth_frequencySq μ) (hasTemperateGrowth_multiplier r hμ) a

lemma frequencySqOperator_cosEvolution {μ : ℝ} (hμ : 0 ≤ μ) (r : ℝ) (a : 𝓢(E, F)) :
    frequencySqOperator F μ (cosEvolution F r μ a) =
      cosEvolution F r μ (frequencySqOperator F μ a) :=
  multiplier_comm F (hasTemperateGrowth_frequencySq μ) (hasTemperateGrowth_cosMultiplier r hμ) a

/-- The velocity has the time derivative `-ω² u`. -/
lemma hasDerivAt_evolveV {μ : ℝ} (hμ : 0 ≤ μ) (a b : 𝓢(E, F)) (x : E) (τ : ℝ) :
    HasDerivAt (fun r => evolveV μ r a b x)
      (-(frequencySqOperator F μ (evolveU μ τ a b) x)) τ := by
  have h := (hasDerivAt_cosEvolution_apply hμ b x τ).sub
    (hasDerivAt_sineEvolution_apply hμ (frequencySqOperator F μ a) x τ)
  have e : ∀ r, evolveV μ r a b x =
      cosEvolution F r μ b x - sineEvolution F r μ (frequencySqOperator F μ a) x := by
    intro r
    simp only [evolveV, sub_apply, frequencySqOperator_sineEvolution hμ]
  simp_rw [e]
  convert h using 1
  simp only [evolveU, map_add, add_apply, frequencySqOperator_cosEvolution hμ]
  abel

open LineDeriv in
lemma lineDeriv_evolveU {μ : ℝ} (hμ : 0 ≤ μ) (m : E) (τ : ℝ) (a b : 𝓢(E, F)) :
    ∂_{m} (evolveU μ τ a b) = evolveU μ τ (∂_{m} a) (∂_{m} b) := by
  unfold evolveU
  rw [lineDerivOp_add]
  congr 1
  · exact lineDeriv_fourierMultiplier (hasTemperateGrowth_cosMultiplier τ hμ) m a
  · exact lineDeriv_fourierMultiplier (hasTemperateGrowth_multiplier τ hμ) m b

open LineDeriv in
lemma lineDeriv_evolveV {μ : ℝ} (hμ : 0 ≤ μ) (m : E) (τ : ℝ) (a b : 𝓢(E, F)) :
    ∂_{m} (evolveV μ τ a b) = evolveV μ τ (∂_{m} a) (∂_{m} b) := by
  unfold evolveV
  rw [sub_eq_add_neg, lineDerivOp_add, lineDerivOp_neg, sub_eq_add_neg]
  congr 2
  · exact lineDeriv_fourierMultiplier (hasTemperateGrowth_cosMultiplier τ hμ) m b
  · rw [frequencySqOperator, lineDeriv_fourierMultiplier (hasTemperateGrowth_frequencySq μ) m]
    congr 1
    exact lineDeriv_fourierMultiplier (hasTemperateGrowth_multiplier τ hμ) m a

open Laplacian in
/-- The operator `ω²` is `-Δ + μ` on Schwartz functions. -/
lemma frequencySqOperator_eq (μ : ℝ) (f : 𝓢(E, F)) :
    frequencySqOperator F μ f = -(Δ f) + μ • f := by
  have hn : (fun ξ : E => ‖ξ‖ ^ 2).HasTemperateGrowth := Function.hasTemperateGrowth_norm_sq E
  have hnC : (fun ξ : E => ((‖ξ‖ ^ 2 : ℝ) : ℂ)).HasTemperateGrowth :=
    Complex.hasTemperateGrowth_ofReal.comp hn
  have hc : (fun _ : E => ((μ : ℝ) : ℂ)).HasTemperateGrowth := Function.HasTemperateGrowth.const _
  rw [SchwartzMap.laplacian_eq_fourierMultiplierCLM, ← SchwartzMap.fourierMultiplierCLM_ofReal ℂ hn]
  have hf : (frequencySq μ : E → ℂ) = (((2 * π) ^ 2 : ℝ) : ℂ) • (fun ξ : E => ((‖ξ‖ ^ 2 : ℝ) : ℂ)) +
      (fun _ => ((μ : ℝ) : ℂ)) := by
    funext ξ; simp only [frequencySq, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; push_cast; ring
  have hsm : ((((2 * π) ^ 2 : ℝ) : ℂ) • (fun ξ : E => ((‖ξ‖ ^ 2 : ℝ) : ℂ))).HasTemperateGrowth :=
    (Function.HasTemperateGrowth.const _).mul hnC
  rw [frequencySqOperator, hf, fourierMultiplierCLM_add F hsm hc,
    SchwartzMap.fourierMultiplierCLM_smul (𝕜 := ℂ) (F := F) hnC]
  have h1 := SchwartzMap.fourierMultiplierCLM_const (𝕜 := ℂ) (F := (F)) (E := E) ((μ : ℝ) : ℂ)
  simp only [smul_apply, neg_smul, neg_neg]
  rw [h1]
  simp only [smul_apply, ContinuousLinearMap.id_apply]
  congr 1

omit [CompleteSpace F] in
lemma continuous_sineEvolution_apply' {μ : ℝ} (hμ : 0 ≤ μ) (a : 𝓢(E, F)) :
    Continuous fun p : ℝ × E => sineEvolution F p.1 μ a p.2 := by
  refine continuous_multiplierFamily_apply a (fun r => multiplier r μ)
    (continuous_multiplier_uncurry μ) (fun r => hasTemperateGrowth_multiplier r hμ) fun R => ?_
  refine ⟨fun ξ => max R 0 * ‖𝓕 a ξ‖,
    ((𝓕 a).integrable (μ := MeasureTheory.volume)).norm.const_mul _, fun r ξ hr => ?_⟩
  exact mul_le_mul_of_nonneg_right ((norm_multiplier_le r μ ξ).trans (hr.trans (le_max_left _ _)))
    (norm_nonneg _)

omit [CompleteSpace F] in
lemma continuous_cosEvolution_apply {μ : ℝ} (hμ : 0 ≤ μ) (a : 𝓢(E, F)) :
    Continuous fun p : ℝ × E => cosEvolution F p.1 μ a p.2 := by
  refine continuous_multiplierFamily_apply a (fun r => cosMultiplier r μ)
    (continuous_cosMultiplier_uncurry μ) (fun r => hasTemperateGrowth_cosMultiplier r hμ)
    fun R => ?_
  refine ⟨fun ξ => ‖𝓕 a ξ‖, ((𝓕 a).integrable (μ := MeasureTheory.volume)).norm, fun r ξ hr => ?_⟩
  have : ‖cosMultiplier r μ ξ‖ ≤ 1 := by
    rw [cosMultiplier, Complex.norm_real, Real.norm_eq_abs]; exact abs_cos_le_one _
  calc ‖cosMultiplier r μ ξ‖ * ‖𝓕 a ξ‖ ≤ 1 * ‖𝓕 a ξ‖ :=
        mul_le_mul_of_nonneg_right this (norm_nonneg _)
    _ = _ := one_mul _

lemma continuous_frequencySqSine_apply {μ : ℝ} (hμ : 0 ≤ μ) (a : 𝓢(E, F)) :
    Continuous fun p : ℝ × E => frequencySqOperator F μ (sineEvolution F p.1 μ a) p.2 := by
  have hw := hasTemperateGrowth_frequencySq (E := E) μ
  have hcomp : ∀ r, frequencySqOperator F μ (sineEvolution F r μ a) =
      SchwartzMap.fourierMultiplierCLM F (frequencySq μ * multiplier r μ) a := fun r =>
    SchwartzMap.fourierMultiplierCLM_fourierMultiplierCLM_apply hw
      (hasTemperateGrowth_multiplier r hμ) a
  simp_rw [hcomp]
  refine continuous_multiplierFamily_apply a (fun r => frequencySq μ * multiplier r μ)
    ((continuous_frequencySq.comp continuous_snd).mul (continuous_multiplier_uncurry μ))
    (fun r => hw.mul (hasTemperateGrowth_multiplier r hμ)) fun R => ?_
  have h0 := ((𝓕 a).integrable (μ := MeasureTheory.volume)).norm
  have h2 : MeasureTheory.Integrable (fun ξ : E => ‖ξ‖ ^ 2 * ‖𝓕 a ξ‖) MeasureTheory.volume :=
    SchwartzMap.integrable_pow_mul MeasureTheory.volume (𝓕 a) 2
  refine ⟨fun ξ => max R 0 * ((2 * π) ^ 2 * (‖ξ‖ ^ 2 * ‖𝓕 a ξ‖) + μ * ‖𝓕 a ξ‖),
    ((h2.const_mul _).add (h0.const_mul _)).const_mul _, fun r ξ hr => ?_⟩
  have hfs : ‖frequencySq μ ξ‖ = (2 * π) ^ 2 * ‖ξ‖ ^ 2 + μ := by
    rw [frequencySq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  simp only [Pi.mul_apply, norm_mul, hfs]
  calc ((2 * π) ^ 2 * ‖ξ‖ ^ 2 + μ) * ‖multiplier r μ ξ‖ * ‖𝓕 a ξ‖
      ≤ ((2 * π) ^ 2 * ‖ξ‖ ^ 2 + μ) * max R 0 * ‖𝓕 a ξ‖ := by
        gcongr
        exact (norm_multiplier_le r μ ξ).trans (hr.trans (le_max_left _ _))
    _ = _ := by ring

omit [CompleteSpace F] in
lemma continuous_evolveU_apply {μ : ℝ} (hμ : 0 ≤ μ) (a b : 𝓢(E, F)) :
    Continuous fun p : ℝ × E => evolveU μ p.1 a b p.2 :=
  (continuous_cosEvolution_apply hμ a).add (continuous_sineEvolution_apply' hμ b)

lemma continuous_evolveV_apply {μ : ℝ} (hμ : 0 ≤ μ) (a b : 𝓢(E, F)) :
    Continuous fun p : ℝ × E => evolveV μ p.1 a b p.2 :=
  (continuous_cosEvolution_apply hμ b).sub (continuous_frequencySqSine_apply hμ a)
end

end KleinGordon
