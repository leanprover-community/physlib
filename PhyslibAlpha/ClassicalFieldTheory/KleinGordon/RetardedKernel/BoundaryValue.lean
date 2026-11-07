/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.KleinGordon.Multiplier
public import PhyslibAlpha.ClassicalFieldTheory.KleinGordon.FreeEvolution
public import PhyslibAlpha.ClassicalFieldTheory.KleinGordon.RetardedKernel.Tempered
public import PhyslibAlpha.Mathematics.Distribution.TimeSliceFourier
public import PhyslibAlpha.Mathematics.SpecialFunctions.SincPropagator.Resolvent

/-!

# The retarded kernel as a boundary value in the spacetime Fourier variables

The retarded kernel tested against a test function is the limit of an integral of the spacetime
Fourier transform against `1 / (ω_ξ² - (2π w + i ε)²)`.

## i. Overview

Time and space are Fourier transformed in this order. The spatial transform of a slice is a
smooth compactly supported function of the time. Fourier inversion in the time writes it as an
integral over the frequency `w` (see `TimeSlice.spaceFourier_eq_integral`). The Laplace transform
of the sine propagation function turns the damped time integral into
`1 / (ω_ξ² - (2π w + i ε)²)`. The damping is removed by dominated convergence. The result is
the boundary value `ε → 0+` of the resolvent, as a statement about the pairing of the retarded
kernel with a test function.

## ii. Key results

- `dampedKernel_eq` : the damped kernel in the spacetime Fourier variables.
- `tendsto_dampedKernel` : the damping can be removed.
- `tendsto_retardedPointSource` : the retarded kernel is the boundary value of the resolvent.
- `solution_zero_eq_advancedSolution_zero` : off the mass shell the retarded and the advanced
  solution agree at the origin.
- `retardedGreen_eq_advancedGreen_of_avoidsShell` : the causal propagator `E = R - A` vanishes at
  the origin for sources whose transform avoids the mass shell.

## iii. Table of contents

- A. The damped kernel
- B. The boundary value
- C. The mass shell

## iv. References

None.

## A. The damped kernel

- `dampedKernel_eq` : the damped kernel in the spacetime Fourier variables.

## B. The boundary value

- `tendsto_dampedKernel` : the damping can be removed.
- `tendsto_retardedPointSource` : the retarded kernel is the boundary value of the resolvent.

## C. The mass shell

- `dampedKernel_zero_eq_of_avoidsShell` : the kernel off the mass shell.
- `solution_zero_eq_advancedSolution_zero` : off the mass shell the retarded and the advanced
  solution agree at the origin.
- `retardedGreen_eq_advancedGreen_of_avoidsShell` : the causal propagator vanishes at the origin
  for sources whose transform avoids the mass shell.
-/

@[expose] public section

noncomputable section

open scoped SchwartzMap FourierTransform ContDiff Distributions
open MeasureTheory TestFunction TimeSlice TopologicalSpace

namespace KleinGordon

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]

/-- The damped time integral of the sine evolution at the origin. -/
def dampedKernel (μ ε : ℝ) (ψ : 𝓓((⊤ : Opens (ℝ × E)), ℂ)) : ℂ :=
  ∫ s in Set.Ioi (0 : ℝ), (Real.exp (-(ε * s)) : ℂ) * sineEvolution ℂ s μ (slice ℂ ψ s) 0

/-- The sine evolution at the origin is the integral of the multiplier against the transform. -/
lemma sineEvolution_zero_eq {μ : ℝ} (hμ : 0 ≤ μ) (ψ : 𝓓((⊤ : Opens (ℝ × E)), ℂ)) (s : ℝ) :
    sineEvolution ℂ s μ (slice ℂ ψ s) 0 = ∫ ξ : E, multiplier s μ ξ * spaceFourier ψ ξ s := by
  rw [sineEvolution_apply_eq ℂ s hμ]
  simp [spaceFourier]

/-- The integrand of the damped kernel is integrable in time and frequency. -/
lemma integrable_dampedIntegrand {μ : ℝ} (ε : ℝ) (ψ : 𝓓((⊤ : Opens (ℝ × E)), ℂ)) :
    Integrable (fun p : ℝ × E => (Real.exp (-(ε * p.1)) : ℂ) *
      (multiplier p.1 μ p.2 * spaceFourier ψ p.2 p.1))
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume) := by
  obtain ⟨K, hK⟩ := exists_fourier_decay ℂ ψ
  obtain ⟨R, hR⟩ := (isCompact_timeSupport ℂ ψ).isBounded.exists_norm_le
  set T : Set ℝ := Prod.fst '' tsupport ψ with hT
  have hTc : IsCompact T := isCompact_timeSupport ℂ ψ
  have hcont : Continuous fun p : ℝ × E => (Real.exp (-(ε * p.1)) : ℂ) *
      (multiplier p.1 μ p.2 * spaceFourier ψ p.2 p.1) := by
    have h1 : Continuous fun p : ℝ × E => (Real.exp (-(ε * p.1)) : ℂ) :=
      Complex.continuous_ofReal.comp (Real.continuous_exp.comp
        (continuous_const.mul continuous_fst).neg)
    have h2 : Continuous fun p : ℝ × E => multiplier p.1 μ p.2 := by
      simp only [multiplier]
      refine Complex.continuous_ofReal.comp (Real.continuous_sincPropagator.comp
        (continuous_fst.prodMk ?_))
      fun_prop
    have h3 : Continuous fun p : ℝ × E => spaceFourier ψ p.2 p.1 :=
      continuous_fourier_slice ℂ ψ
    exact h1.mul (h2.mul h3)
  have hind : Integrable (T.indicator fun _ : ℝ => Real.exp (|ε| * R) * R)
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    ((integrableOn_const hTc.measure_lt_top.ne).integrable_indicator
      hTc.measurableSet).integrableOn
  have hn : (Module.finrank ℝ E : ℝ) < ((Module.finrank ℝ E + 1 : ℕ) : ℝ) := by push_cast; linarith
  have hE : Integrable (fun ξ : E => K * (1 + ‖ξ‖) ^ (-((Module.finrank ℝ E + 1 : ℕ) : ℝ))) :=
    (integrable_one_add_norm hn).const_mul K
  refine (hind.mul_prod hE).mono' hcont.aestronglyMeasurable
    (Filter.Eventually.of_forall fun p => ?_)
  obtain ⟨s, ξ⟩ := p
  by_cases hs : s ∈ T
  · rw [Set.indicator_of_mem hs]
    have hsR : |s| ≤ R := by simpa using hR s hs
    have h1 : ‖(Real.exp (-(ε * s)) : ℂ)‖ ≤ Real.exp (|ε| * R) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      refine Real.exp_le_exp.2 ?_
      calc -(ε * s) ≤ |ε * s| := neg_le_abs _
        _ = |ε| * |s| := abs_mul _ _
        _ ≤ |ε| * R := by gcongr
    have h2 : ‖multiplier s μ ξ‖ ≤ R := (norm_multiplier_le s μ ξ).trans hsR
    have h3 : ‖spaceFourier ψ ξ s‖ ≤ K * (1 + ‖ξ‖) ^ (-((Module.finrank ℝ E + 1 : ℕ) : ℝ)) :=
      hK s ξ
    have hR0 : 0 ≤ R := (abs_nonneg s).trans hsR
    have hK0 : 0 ≤ K * (1 + ‖ξ‖) ^ (-((Module.finrank ℝ E + 1 : ℕ) : ℝ)) :=
      (norm_nonneg _).trans h3
    simp only [norm_mul]
    calc ‖(Real.exp (-(ε * s)) : ℂ)‖ * (‖multiplier s μ ξ‖ * ‖spaceFourier ψ ξ s‖)
        ≤ Real.exp (|ε| * R) * (R * (K * (1 + ‖ξ‖) ^ (-((Module.finrank ℝ E + 1 : ℕ) : ℝ)))) := by
          gcongr
      _ = _ := by ring
  · rw [Set.indicator_of_notMem hs]
    have : spaceFourier ψ ξ s = 0 := by simp [spaceFourier, slice_eq_zero_of_notMem ℂ ψ hs]
    simp [this]

/-- **The damped kernel in the spacetime Fourier variables.** The damped time integral of the
sine evolution at the origin is the integral of the transform against
`1 / (ω_ξ² - (2π w + i ε)²)`. -/
lemma dampedKernel_eq {μ ε : ℝ} (hμ : 0 ≤ μ) (hε : 0 < ε)
    (ψ : 𝓓((⊤ : Opens (ℝ × E)), ℂ)) :
    dampedKernel μ ε ψ = ∫ ξ : E, ∫ w : ℝ, timeFourier ψ w ξ *
      (1 / ((dispersion μ ξ : ℂ) ^ 2 - (2 * Real.pi * w + ε * Complex.I) ^ 2)) := by
  have hswap := integral_integral_swap (f := fun (s : ℝ) (ξ : E) =>
    (Real.exp (-(ε * s)) : ℂ) * (multiplier s μ ξ * spaceFourier ψ ξ s))
    (integrable_dampedIntegrand ε ψ)
  calc dampedKernel μ ε ψ
      = ∫ s in Set.Ioi (0 : ℝ), ∫ ξ : E, (Real.exp (-(ε * s)) : ℂ) *
          (multiplier s μ ξ * spaceFourier ψ ξ s) := by
        refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
        rw [sineEvolution_zero_eq hμ, integral_const_mul]
    _ = ∫ ξ : E, ∫ s in Set.Ioi (0 : ℝ), (Real.exp (-(ε * s)) : ℂ) *
          (multiplier s μ ξ * spaceFourier ψ ξ s) := hswap
    _ = _ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
        exact Real.integral_damped_sincPropagator hε (dispersion μ ξ) (spaceFourierSchwartz ψ ξ)

/-- **The damping can be removed.** The damped kernel converges to the undamped one. -/
lemma tendsto_dampedKernel {μ : ℝ} (hμ : 0 ≤ μ) (ψ : 𝓓((⊤ : Opens (ℝ × E)), ℂ)) :
    Filter.Tendsto (fun ε => dampedKernel μ ε ψ) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (dampedKernel μ 0 ψ)) := by
  obtain ⟨K, hK⟩ := exists_fourier_decay ℂ ψ
  obtain ⟨R, hR⟩ := (isCompact_timeSupport ℂ ψ).isBounded.exists_norm_le
  set T : Set ℝ := Prod.fst '' tsupport ψ with hT
  have hTc : IsCompact T := isCompact_timeSupport ℂ ψ
  have hn : (Module.finrank ℝ E : ℝ) < ((Module.finrank ℝ E + 1 : ℕ) : ℝ) := by
    push_cast; linarith
  have hE : Integrable (fun ξ : E => K * (1 + ‖ξ‖) ^ (-((Module.finrank ℝ E + 1 : ℕ) : ℝ))) :=
    (integrable_one_add_norm hn).const_mul K
  set B : ℝ := R * ∫ ξ : E, K * (1 + ‖ξ‖) ^ (-((Module.finrank ℝ E + 1 : ℕ) : ℝ)) with hB
  have hbound : ∀ s : ℝ, ‖sineEvolution ℂ s μ (slice ℂ ψ s) 0‖ ≤ T.indicator (fun _ => B) s := by
    intro s
    by_cases hs : s ∈ T
    · rw [Set.indicator_of_mem hs, sineEvolution_zero_eq hμ, hB]
      have hsR : |s| ≤ R := by simpa using hR s hs
      rw [← integral_const_mul]
      refine norm_integral_le_of_norm_le (hE.const_mul R) (Filter.Eventually.of_forall fun ξ => ?_)
      have h1 : ‖multiplier s μ ξ‖ ≤ R := (norm_multiplier_le s μ ξ).trans hsR
      have h3 := hK s ξ
      rw [norm_mul]
      have hK0 : 0 ≤ K * (1 + ‖ξ‖) ^ (-((Module.finrank ℝ E + 1 : ℕ) : ℝ)) :=
        (norm_nonneg _).trans h3
      have hR0 : 0 ≤ R := (abs_nonneg s).trans hsR
      gcongr
      exact h3
    · rw [Set.indicator_of_notMem hs]
      simp [slice_eq_zero_of_notMem ℂ ψ hs]
  have hind : Integrable (T.indicator fun _ : ℝ => Real.exp R * B) :=
    (integrableOn_const hTc.measure_lt_top.ne).integrable_indicator hTc.measurableSet
  refine tendsto_integral_filter_of_dominated_convergence
    (bound := T.indicator fun _ => Real.exp R * B) ?_ ?_ hind.integrableOn ?_
  · refine Filter.Eventually.of_forall fun ε => ?_
    have h := (integrable_dampedIntegrand (μ := μ) ε ψ).integral_prod_left
    refine h.aestronglyMeasurable.congr (Filter.Eventually.of_forall fun s => ?_)
    simp only
    rw [integral_const_mul, ← sineEvolution_zero_eq hμ]
  · filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with ε hε
    refine Filter.Eventually.of_forall fun s => ?_
    by_cases hs : s ∈ T
    · rw [Set.indicator_of_mem hs]
      have hsR : |s| ≤ R := by simpa using hR s hs
      have h1 : ‖(Real.exp (-(ε * s)) : ℂ)‖ ≤ Real.exp R := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        refine Real.exp_le_exp.2 ?_
        calc -(ε * s) ≤ |ε * s| := neg_le_abs _
          _ = |ε| * |s| := abs_mul _ _
          _ ≤ 1 * R := by
            rw [abs_of_pos hε.1]
            gcongr
            exact hε.2.le
          _ = R := one_mul _
      rw [norm_mul]
      have h2 := hbound s
      rw [Set.indicator_of_mem hs] at h2
      gcongr
    · rw [Set.indicator_of_notMem hs]
      have h2 := hbound s
      rw [Set.indicator_of_notMem hs] at h2
      have : ‖sineEvolution ℂ s μ (slice ℂ ψ s) 0‖ = 0 := le_antisymm h2 (norm_nonneg _)
      simp [this]
  · refine Filter.Eventually.of_forall fun s => ?_
    have hc : Continuous fun ε : ℝ => (Real.exp (-(ε * s)) : ℂ) *
        sineEvolution ℂ s μ (slice ℂ ψ s) 0 :=
      (Complex.continuous_ofReal.comp (Real.continuous_exp.comp
        (continuous_id.mul continuous_const).neg)).mul continuous_const
    exact (hc.tendsto 0).mono_left nhdsWithin_le_nhds

/-- The damped kernel without damping is the advanced solution at the origin. -/
lemma dampedKernel_zero_eq {μ : ℝ} (hμ : 0 ≤ μ) (ψ : 𝓓((⊤ : Opens (ℝ × E)), ℂ)) :
    dampedKernel μ 0 ψ = advancedSolution ℂ ψ μ 0 0 := by
  have h := advancedSolution_eq_integral ℂ ψ hμ 0 0
  rw [h]
  simp [dampedKernel]

/-- The retarded solution at the origin is the undamped kernel of the reflected source. -/
lemma solution_zero_eq {μ : ℝ} (hμ : 0 ≤ μ) (ψ : 𝓓((⊤ : Opens (ℝ × E)), ℂ)) :
    solution ℂ ψ μ 0 0 = dampedKernel μ 0 (reflect ℂ ψ) := by
  rw [dampedKernel_zero_eq hμ]
  unfold advancedSolution
  rw [TimeSlice.reflect_reflect]
  simp

/-- The resolvent of the Klein–Gordon operator at the complexified frequency `2π w + i ε`. -/
def resolvent (μ ε w : ℝ) (ξ : E) : ℂ :=
  1 / ((dispersion μ ξ : ℂ) ^ 2 - (2 * Real.pi * w + ε * Complex.I) ^ 2)

/-- The test function has no Fourier support within `δ` of the mass shell. -/
def AvoidsShell (μ δ : ℝ) (χ : 𝓓((⊤ : Opens (ℝ × E)), ℂ)) : Prop :=
  ∀ (w : ℝ) (ξ : E), |dispersion μ ξ ^ 2 - (2 * Real.pi * w) ^ 2| < δ → timeFourier χ w ξ = 0

lemma norm_mul_resolvent_le {μ δ : ℝ} (hδ : 0 < δ) {χ : 𝓓((⊤ : Opens (ℝ × E)), ℂ)}
    (hχ : AvoidsShell μ δ χ) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hεδ : ε ≤ δ / 2)
    (w : ℝ) (ξ : E) :
    ‖timeFourier χ w ξ * resolvent μ ε w ξ‖ ≤ ‖timeFourier χ w ξ‖ * (2 / δ) := by
  by_cases h : timeFourier χ w ξ = 0
  · simp [h]
  · rw [norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have h1 : δ ≤ |dispersion μ ξ ^ 2 - (2 * Real.pi * w) ^ 2| := by
      by_contra hlt
      exact h (hχ w ξ (not_le.mp hlt))
    have := Real.norm_resolvent_le (A := dispersion μ ξ ^ 2) hδ hε0 hε1 hεδ h1
    simpa [resolvent] using this

lemma measurable_resolvent (μ ε : ℝ) : Measurable fun p : ℝ × E => resolvent μ ε p.1 p.2 := by
  have hd : Continuous fun ξ : E => dispersion μ ξ := by
    unfold dispersion
    fun_prop
  have hdm : Measurable fun p : ℝ × E => (dispersion μ p.2 : ℂ) :=
    (Complex.continuous_ofReal.comp (hd.comp continuous_snd)).measurable
  have hw : Measurable fun p : ℝ × E => (2 * Real.pi * (p.1 : ℂ) + ε * Complex.I) ^ 2 := by
    fun_prop
  exact measurable_const.div ((hdm.pow_const 2).sub hw)

lemma aestronglyMeasurable_timeFourier_mul_resolvent (χ : 𝓓((⊤ : Opens (ℝ × E)), ℂ))
    (μ ε : ℝ) (ξ : E) :
    AEStronglyMeasurable (fun w : ℝ => timeFourier χ w ξ * resolvent μ ε w ξ) volume := by
  have h0 : Continuous fun w : ℝ => ((w, ξ) : ℝ × E) := by fun_prop
  have h1 : Continuous fun w : ℝ => timeFourier χ w ξ := by
    have := (continuous_timeFourier χ).comp h0
    exact this
  have h2 : Measurable fun w : ℝ => resolvent μ ε w ξ := by
    have := (measurable_resolvent (E := E) μ ε).comp h0.measurable
    exact this
  exact (h1.measurable.mul h2).aestronglyMeasurable

/-- Inner dominated convergence: the resolvent integral converges off the mass shell. -/
lemma tendsto_integral_resolvent {μ δ : ℝ} (hδ : 0 < δ) {χ : 𝓓((⊤ : Opens (ℝ × E)), ℂ)}
    (hχ : AvoidsShell μ δ χ) (ξ : E) :
    Filter.Tendsto (fun ε : ℝ => ∫ w : ℝ, timeFourier χ w ξ * resolvent μ ε w ξ)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (∫ w : ℝ, timeFourier χ w ξ * resolvent μ 0 w ξ)) := by
  have hmeas : ∀ ε : ℝ, AEStronglyMeasurable
      (fun w : ℝ => timeFourier χ w ξ * resolvent μ ε w ξ) volume := fun ε =>
    (aestronglyMeasurable_timeFourier_mul_resolvent χ μ ε ξ)
  refine tendsto_integral_filter_of_dominated_convergence
    (fun w => ‖timeFourier χ w ξ‖ * (2 / δ)) ?_ ?_ ((integrable_timeFourier χ ξ).norm.mul_const _)
    ?_
  · exact Filter.Eventually.of_forall hmeas
  · filter_upwards [Ioo_mem_nhdsGT (lt_min (zero_lt_one' ℝ) (half_pos hδ))] with ε hε
    exact Filter.Eventually.of_forall fun w => norm_mul_resolvent_le hδ hχ hε.1.le
      (hε.2.trans_le (min_le_left _ _)).le (hε.2.trans_le (min_le_right _ _)).le w ξ
  · refine Filter.Eventually.of_forall fun w => ?_
    by_cases h : timeFourier χ w ξ = 0
    · simp [h]
    · have h1 : δ ≤ |dispersion μ ξ ^ 2 - (2 * Real.pi * w) ^ 2| := by
        by_contra hlt
        exact h (hχ w ξ (not_le.mp hlt))
      have hne : ((dispersion μ ξ : ℂ) ^ 2 - (2 * Real.pi * w + (0 : ℝ) * Complex.I) ^ 2) ≠ 0 := by
        intro h0
        have : (dispersion μ ξ : ℝ) ^ 2 - (2 * Real.pi * w) ^ 2 = 0 := by
          have := congrArg Complex.re h0
          simpa [pow_two] using this
        rw [this, abs_zero] at h1
        linarith
      have hc : ContinuousAt (fun ε : ℝ => timeFourier χ w ξ * resolvent μ ε w ξ) 0 := by
        unfold resolvent
        refine continuousAt_const.mul (continuousAt_const.div ?_ hne)
        fun_prop
      exact hc.tendsto.mono_left nhdsWithin_le_nhds

lemma aestronglyMeasurable_integral_timeFourier_mul_resolvent
    (χ : 𝓓((⊤ : Opens (ℝ × E)), ℂ)) (μ ε : ℝ) :
    AEStronglyMeasurable (fun ξ : E => ∫ w : ℝ, timeFourier χ w ξ * resolvent μ ε w ξ)
      volume := by
  have h1 : Continuous fun q : E × ℝ => timeFourier χ q.2 q.1 := by
    have := (continuous_timeFourier χ).comp (continuous_swap (X := E) (Y := ℝ))
    exact this
  have h2 : Measurable fun q : E × ℝ => resolvent μ ε q.2 q.1 := by
    have := (measurable_resolvent (E := E) μ ε).comp (measurable_swap (α := E) (β := ℝ))
    exact this
  have hj : AEStronglyMeasurable
      (fun q : E × ℝ => timeFourier χ q.2 q.1 * resolvent μ ε q.2 q.1) (volume.prod volume) :=
    (h1.measurable.mul h2).aestronglyMeasurable
  exact hj.integral_prod_right'

lemma norm_integral_timeFourier_mul_resolvent_le {μ δ : ℝ} (hδ : 0 < δ)
    {χ : 𝓓((⊤ : Opens (ℝ × E)), ℂ)} (hχ : AvoidsShell μ δ χ) {ε : ℝ} (h1 : 0 ≤ ε) (h2 : ε ≤ 1)
    (h3 : ε ≤ δ / 2) (C : ℝ) (n : ℕ)
    (hC : ∀ ξ : E, ∫ w : ℝ, ‖timeFourier χ w ξ‖ ≤ C * (1 + ‖ξ‖) ^ (-(n : ℝ))) (ξ : E) :
    ‖∫ w : ℝ, timeFourier χ w ξ * resolvent μ ε w ξ‖ ≤
      (2 / δ) * (C * (1 + ‖ξ‖) ^ (-(n : ℝ))) := by
  calc ‖∫ w : ℝ, timeFourier χ w ξ * resolvent μ ε w ξ‖
      ≤ ∫ w : ℝ, ‖timeFourier χ w ξ‖ * (2 / δ) :=
        (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun w => norm_nonneg _)
          ((integrable_timeFourier χ ξ).norm.mul_const _)
          (Filter.Eventually.of_forall fun w => norm_mul_resolvent_le hδ hχ h1 h2 h3 w ξ))
    _ = (∫ w : ℝ, ‖timeFourier χ w ξ‖) * (2 / δ) := integral_mul_const _ _
    _ ≤ (C * (1 + ‖ξ‖) ^ (-(n : ℝ))) * (2 / δ) := by
        gcongr
        exact hC ξ
    _ = _ := by ring

/-- **The kernel off the mass shell.** If the transform of the source vanishes near the mass shell
then the undamped kernel is the integral of the transform against the unregularised resolvent. -/
lemma dampedKernel_zero_eq_of_avoidsShell {μ δ : ℝ} (hμ : 0 ≤ μ) (hδ : 0 < δ)
    {χ : 𝓓((⊤ : Opens (ℝ × E)), ℂ)} (hχ : AvoidsShell μ δ χ) :
    dampedKernel μ 0 χ = ∫ ξ : E, ∫ w : ℝ, timeFourier χ w ξ * resolvent μ 0 w ξ := by
  obtain ⟨C, hC0, hC⟩ := exists_integral_norm_timeFourier_le χ (Module.finrank ℝ E + 1)
  have hn : (Module.finrank ℝ E : ℝ) < ((Module.finrank ℝ E + 1 : ℕ) : ℝ) := by
    push_cast; linarith
  have hbd : Integrable (fun ξ : E => (2 / δ) *
      (C * (1 + ‖ξ‖) ^ (-((Module.finrank ℝ E + 1 : ℕ) : ℝ)))) :=
    ((integrable_one_add_norm hn).const_mul C).const_mul _
  have hlim : Filter.Tendsto (fun ε : ℝ => ∫ ξ : E, ∫ w : ℝ,
      timeFourier χ w ξ * resolvent μ ε w ξ) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∫ ξ : E, ∫ w : ℝ, timeFourier χ w ξ * resolvent μ 0 w ξ)) := by
    refine tendsto_integral_filter_of_dominated_convergence _ ?_ ?_ hbd ?_
    · exact Filter.Eventually.of_forall fun ε =>
        aestronglyMeasurable_integral_timeFourier_mul_resolvent χ μ ε
    · filter_upwards [Ioo_mem_nhdsGT (lt_min (zero_lt_one' ℝ) (half_pos hδ))] with ε hε
      exact Filter.Eventually.of_forall fun ξ => norm_integral_timeFourier_mul_resolvent_le hδ hχ
        hε.1.le (hε.2.trans_le (min_le_left _ _)).le (hε.2.trans_le (min_le_right _ _)).le C _
        hC ξ
    · exact Filter.Eventually.of_forall fun ξ => tendsto_integral_resolvent hδ hχ ξ
  have hT := tendsto_dampedKernel hμ χ
  refine tendsto_nhds_unique hT (hlim.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [dampedKernel_eq hμ hε]
  rfl

lemma avoidsShell_reflect {μ δ : ℝ} {χ : 𝓓((⊤ : Opens (ℝ × E)), ℂ)} (h : AvoidsShell μ δ χ) :
    AvoidsShell μ δ (reflect ℂ χ) := fun w ξ hw => by
  rw [timeFourier_reflect]
  exact h (-w) ξ (by simpa using hw)

/-- **The retarded and the advanced solution agree off the mass shell.** If the transform of the
source vanishes within `δ` of the mass shell then the retarded and the advanced solution have the
same value at the origin. -/
lemma solution_zero_eq_advancedSolution_zero {μ δ : ℝ} (hμ : 0 ≤ μ) (hδ : 0 < δ)
    {χ : 𝓓((⊤ : Opens (ℝ × E)), ℂ)} (hχ : AvoidsShell μ δ χ) :
    solution ℂ χ μ 0 0 = advancedSolution ℂ χ μ 0 0 := by
  rw [solution_zero_eq hμ, ← dampedKernel_zero_eq hμ,
    dampedKernel_zero_eq_of_avoidsShell hμ hδ (avoidsShell_reflect hχ),
    dampedKernel_zero_eq_of_avoidsShell hμ hδ hχ]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [timeFourier_reflect]
  rw [← integral_neg_eq_self (fun w : ℝ => timeFourier χ w ξ * resolvent μ 0 w ξ)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp [resolvent]

end KleinGordon

namespace KleinGordon.Spacetime

open KleinGordon Minkowski

variable {d : ℕ}

/-- The retarded kernel is the real part of the undamped kernel of the transported source. -/
lemma retardedPointSource_zero_eq (m : ℝ) (φ : 𝓓((⊤ : Opens (SpaceTime d)), ℝ)) :
    retardedPointSource m (0 : SpaceTime d) φ =
      (dampedKernel (m ^ 2) 0
        (sourceEquiv ℂ (TestFunction.postcompCLM Complex.ofRealCLM φ))).re := by
  have h0 : coordinates d (0 : SpaceTime d) = (0, 0) := by rw [map_zero]; rfl
  rw [retardedPointSource_apply, h0]
  congr 1
  simp only [dampedKernel, neg_zero, zero_mul, Real.exp_zero, Complex.ofReal_one, one_mul,
    sub_zero]
  exact setIntegral_congr_fun measurableSet_Ioi fun s _ =>
    (sineEvolution_apply_eq_delta (sq_nonneg m) s _ 0).symm

/-- The advanced kernel is the real part of the retarded solution of the transported source. -/
lemma advancedPointSource_zero_eq (m : ℝ) (φ : 𝓓((⊤ : Opens (SpaceTime d)), ℝ)) :
    advancedPointSource m (0 : SpaceTime d) φ =
      (solution ℂ (sourceEquiv ℂ (TestFunction.postcompCLM Complex.ofRealCLM φ)) (m ^ 2) 0
        0).re := by
  have h0 : coordinates d (0 : SpaceTime d) = (0, 0) := by rw [map_zero]; rfl
  change (retardedResponse ℂ (m ^ 2) (TestFunction.postcompCLM Complex.ofRealCLM φ) 0).re = _
  rw [retardedResponse, h0]

/-- **On the mass shell.** If the spacetime Fourier transform of a test function vanishes within
`δ` of the mass shell then the retarded and the advanced kernel give the same value. So the
Fourier transform of the causal propagator `E = R - A` is supported on the mass shell. -/
lemma advancedPointSource_eq_retardedPointSource_of_avoidsShell (m δ : ℝ) (hδ : 0 < δ)
    (φ : 𝓓((⊤ : Opens (SpaceTime d)), ℝ))
    (h : AvoidsShell (m ^ 2) δ (sourceEquiv ℂ (TestFunction.postcompCLM Complex.ofRealCLM φ))) :
    advancedPointSource m (0 : SpaceTime d) φ = retardedPointSource m (0 : SpaceTime d) φ := by
  rw [advancedPointSource_zero_eq, retardedPointSource_zero_eq,
    solution_zero_eq_advancedSolution_zero (sq_nonneg m) hδ h, dampedKernel_zero_eq (sq_nonneg m)]

/-- **The retarded kernel is the boundary value of the resolvent.** The retarded kernel tested
against a real test function `φ` is the limit for `ε → 0+` of the integral of the spacetime Fourier
transform of `φ` against `1 / (ω_ξ² - (2π w + i ε)²)`. -/
lemma tendsto_retardedPointSource (m : ℝ) (φ : 𝓓((⊤ : Opens (SpaceTime d)), ℝ)) :
    Filter.Tendsto (fun ε : ℝ => (∫ ξ : Space d, ∫ w : ℝ,
      timeFourier (sourceEquiv ℂ (TestFunction.postcompCLM Complex.ofRealCLM φ)) w ξ *
        (1 / ((dispersion (m ^ 2) ξ : ℂ) ^ 2 - (2 * Real.pi * w + ε * Complex.I) ^ 2))).re)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (retardedPointSource m (0 : SpaceTime d) φ)) := by
  set ψ := sourceEquiv ℂ (TestFunction.postcompCLM Complex.ofRealCLM φ) with hψ
  have h1 := (Complex.continuous_re.tendsto _).comp (tendsto_dampedKernel (sq_nonneg m) ψ)
  have h2 : retardedPointSource m (0 : SpaceTime d) φ = (dampedKernel (m ^ 2) 0 ψ).re := by
    have h0 : coordinates d (0 : SpaceTime d) = (0, 0) := by rw [map_zero]; rfl
    rw [retardedPointSource_apply, h0]
    congr 1
    simp only [dampedKernel, neg_zero, zero_mul, Real.exp_zero, Complex.ofReal_one, one_mul,
      sub_zero]
    exact setIntegral_congr_fun measurableSet_Ioi fun s _ =>
      (sineEvolution_apply_eq_delta (sq_nonneg m) s _ 0).symm
  rw [h2]
  refine h1.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  simp only [Function.comp_apply]
  rw [dampedKernel_eq (sq_nonneg m) hε]

/-- **The causal propagator vanishes off the mass shell.** If the Fourier transform of a real
test source vanishes within `δ` of the mass shell then the retarded and the advanced solution
agree at the origin. So `E f = R f - A f` vanishes at the origin. -/
lemma retardedGreen_eq_advancedGreen_of_avoidsShell (m δ : ℝ) (hδ : 0 < δ) (f : TestField d ℝ)
    (h : AvoidsShell (m ^ 2) δ
      (sourceEquiv ℂ (TestFunction.postcompCLM Complex.ofRealCLM (testFieldEquiv ℝ f)))) :
    ((realRetardedGreenOperator m).toLinearMap f).val 0 =
      ((realAdvancedGreenOperator m).toLinearMap f).val 0 := by
  rw [← realRetardedEvaluation_apply, ← realAdvancedEvaluation_apply]
  exact advancedPointSource_eq_retardedPointSource_of_avoidsShell m δ hδ _ h

end KleinGordon.Spacetime
