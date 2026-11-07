/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.KleinGordon.FinitePropagation
public import PhyslibAlpha.ClassicalFieldTheory.KleinGordon.RetardedSolution
public import PhyslibAlpha.ClassicalFieldTheory.KleinGordon.Smoothness

/-!

# The solution as a tempered distribution in space

## i. Overview

At each time the retarded solution pairs with Schwartz functions through the sine evolution of the
source slices.

## ii. Key results

- `solutionSlice` : The spatial slice of the retarded solution as a Schwartz function.
- `solutionSlice_pairing` : **The retarded solution as a tempered distribution.** Tested against a
  Schwartz function `g` the spatial slice of the retarded solution at the time `t` is the integral
  over the source time `s ≤ t` of the Fourier multiplier `sincPropagator (t - s)` applied to the
  tempered slice of the source.
- `advancedSolution_eq_dirac` : **Advanced response at a point.** The advanced solution at the point
  `(t, y)` is the integral over the later source times of the pairing of the propagated Dirac
  distribution at `y` with the slice of the source.
- `sineEvolution_apply_eq_delta` : The propagation of a Schwartz function at a point is the pairing
  of the propagated Dirac distribution with it.

## iii. Table of contents

- A. The retarded solution as a tempered distribution in space

## iv. References

None.

## A. The retarded solution as a tempered distribution in space

- `solutionSlice` : The spatial slice of the retarded solution as a Schwartz function.

Lemmas: `hasCompactSupport_solution_slice`, `solutionSlice_apply`, `integrable_pairing_integrand`,
`solutionSlice_pairing`, `sineEvolution_apply_eq_delta`, `advancedSolution_eq_integral`,
`advancedSolution_eq_dirac`.

-/

@[expose] public section

noncomputable section

open scoped SchwartzMap Distributions
open Duhamel FourierMultiplier TimeSlice TimeSpace TopologicalSpace Topology MeasureTheory
universe u

namespace KleinGordon

section
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (F : Type u) [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F] (f : 𝓓((⊤ : Opens (ℝ × E)), F))

/-- The spatial slice of the retarded solution has compact support. -/
lemma hasCompactSupport_solution_slice {μ : ℝ} (hμ : 0 ≤ μ) (t : ℝ) :
    HasCompactSupport fun x : E => solution F f μ t x := by
  obtain ⟨R, hR0, hR⟩ := exists_radius F f
  refine HasCompactSupport.intro (K := Metric.closedBall (0 : E) (2 * R + |t|))
    (isCompact_closedBall _ _) fun x hx => ?_
  apply solution_eq_zero_of_not_mem_causalFuture F f hμ
  rintro ⟨q, hq, hle⟩
  have h1 := hR q hq
  have h2 : ‖q.2‖ ≤ R := (norm_snd_le q).trans h1
  have h3 : |q.1| ≤ R := by simpa using (norm_fst_le q).trans h1
  have hx' : 2 * R + |t| < ‖x‖ := by simpa using hx
  have h4 : ‖x‖ ≤ ‖x - q.2‖ + ‖q.2‖ := by
    calc ‖x‖ = ‖(x - q.2) + q.2‖ := by rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
  simp only at hle
  have h5 := le_abs_self t
  have h6 := neg_abs_le q.1
  linarith

/-- The spatial slice of the retarded solution as a Schwartz function. -/
def solutionSlice {μ : ℝ} (hμ : 0 ≤ μ) (t : ℝ) : 𝓢(E, F) :=
  (hasCompactSupport_solution_slice F f hμ t).toSchwartzMap
    ((contDiff_solution F f hμ).comp (contDiff_const.prodMk contDiff_id))

@[simp]
lemma solutionSlice_apply {μ : ℝ} (hμ : 0 ≤ μ) (t : ℝ) (x : E) :
    solutionSlice F f hμ t x = solution F f μ t x := rfl

/-- The integrand of the Duhamel pairing is integrable on the product of space and past times. -/
lemma integrable_pairing_integrand {μ : ℝ} (hμ : 0 ≤ μ) (t : ℝ) (g : 𝓢(E, ℂ)) :
    Integrable (fun q : E × ℝ => g q.1 • sineEvolution F (t - q.2) μ (slice F f q.2) q.1)
      ((volume : Measure E).prod (volume.restrict (Set.Iic t))) := by
  obtain ⟨R, hR0, hR⟩ := exists_radius F f
  obtain ⟨a, ha⟩ := exists_timeBound F f
  have hcont : Continuous fun q : E × ℝ =>
      g q.1 • sineEvolution F (t - q.2) μ (slice F f q.2) q.1 := by
    have hp := (continuous_propagatedSlice F f (fun r ξ => multiplier r μ ξ)
      (continuous_multiplier_uncurry μ)
      (fun R => ⟨R, fun r ξ hr => (norm_multiplier_le r μ ξ).trans hr⟩)).comp
      (show Continuous fun q : E × ℝ => (t - q.2, q.2, q.1) by fun_prop)
    simp_rw [propagatedSlice_eq_sineEvolution F f hμ] at hp
    exact g.continuous.comp continuous_fst |>.smul hp
  have hmeas : (volume : Measure E).prod (volume.restrict (Set.Iic t)) =
      ((volume : Measure E).prod volume).restrict (Set.univ ×ˢ Set.Iic t) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  rw [hmeas]
  have hK : IsCompact (Metric.closedBall (0 : E) (R + |t| + |a|) ×ˢ Set.Icc a t) :=
    (isCompact_closedBall _ _).prod isCompact_Icc
  have hKint : IntegrableOn (fun q : E × ℝ =>
      g q.1 • sineEvolution F (t - q.2) μ (slice F f q.2) q.1)
      (Metric.closedBall (0 : E) (R + |t| + |a|) ×ˢ Set.Icc a t) :=
    hcont.continuousOn.integrableOn_compact hK
  refine (IntegrableOn.of_forall_sdiff_eq_zero hKint (MeasurableSet.univ.prod measurableSet_Iic)
    fun q hq => ?_)
  obtain ⟨-, hqt⟩ := hq.1
  have hnK := hq.2
  have hz : sineEvolution F (t - q.2) μ (slice F f q.2) q.1 = 0 := by
    by_cases hs : q.2 ≤ a
    · rw [← propagatedSlice_eq_sineEvolution F f hμ]
      exact propagatedSlice_eq_zero_of_notMem F f _ _ (ha q.2 hs) q.1
    · push Not at hs
      refine sineEvolution_slice_eq_zero F f hμ hqt fun y hy => ?_
      have hy1 : ‖y‖ ≤ R := (norm_snd_le (q.2, y)).trans (hR _ hy)
      have hx : R + |t| + |a| < ‖q.1‖ := by
        by_contra hle
        exact hnK ⟨by simpa using not_lt.1 hle, ⟨hs.le, hqt⟩⟩
      have h4 : ‖q.1‖ ≤ ‖y - q.1‖ + ‖y‖ := by
        calc ‖q.1‖ = ‖-(y - q.1) + y‖ := by congr 1; abel
          _ ≤ ‖-(y - q.1)‖ + ‖y‖ := norm_add_le _ _
          _ = _ := by rw [norm_neg]
      have h5 := le_abs_self t
      have h6 := neg_abs_le a
      linarith
  simp only [hz, smul_zero]

/-- **The retarded solution as a tempered distribution.** Tested against a Schwartz function `g`
the spatial slice of the retarded solution at the time `t` is the integral over the source time
`s ≤ t` of the Fourier multiplier `sincPropagator (t - s)` applied to the tempered slice of the
source. -/
lemma solutionSlice_pairing {μ : ℝ} (hμ : 0 ≤ μ) (t : ℝ) (g : 𝓢(E, ℂ)) :
    (solutionSlice F f hμ t : 𝓢'(E, F)) g =
      ∫ s in Set.Iic t, sineEvolutionTempered F (t - s) μ (slice F f s : 𝓢'(E, F)) g := by
  have hR : ∀ s ∈ Set.Iic t, sineEvolutionTempered F (t - s) μ (slice F f s : 𝓢'(E, F)) g =
      ∫ x : E, g x • sineEvolution F (t - s) μ (slice F f s) x := by
    intro s _
    rw [sineEvolutionTempered_coe F (t - s) hμ, SchwartzMap.coe_apply]
  rw [setIntegral_congr_fun measurableSet_Iic hR, SchwartzMap.coe_apply]
  simp_rw [solutionSlice_apply, solution_eq_integral F f hμ, ← integral_smul]
  exact integral_integral_swap (f := fun x s => g x • sineEvolution F (t - s) μ (slice F f s) x)
    (integrable_pairing_integrand F f hμ t g)

/-- The propagation of a Schwartz function at a point is the pairing of the propagated Dirac
distribution with it. -/
lemma sineEvolution_apply_eq_delta {μ : ℝ} (hμ : 0 ≤ μ) (r : ℝ) (g : 𝓢(E, ℂ)) (y : E) :
    sineEvolution ℂ r μ g y =
      sineEvolutionTempered ℂ r μ (TemperedDistribution.delta y) g := by
  rw [sineEvolutionTempered, TemperedDistribution.fourierMultiplierCLM_apply_apply,
    TemperedDistribution.delta_apply, sineEvolution, SchwartzMap.fourierMultiplierCLM_apply,
    SchwartzMap.fourierInv_coe, SchwartzMap.fourier_coe]
  have key : ∀ h : 𝓢(E, ℂ), ⇑(SchwartzMap.smulLeftCLM ℂ (multiplier r μ) h) =
      fun x => multiplier r μ x • h x := fun h =>
    funext fun x => SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_multiplier r hμ) h x
  rw [key, key, SchwartzMap.fourier_coe, SchwartzMap.fourierInv_coe]
  exact (fourier_smul_fourierInv_of_even _ (multiplier_neg r μ) _ y).symm

omit [CompleteSpace F] in
/-- The advanced solution is the integral over the later source times. -/
lemma advancedSolution_eq_integral {μ : ℝ} (hμ : 0 ≤ μ) (t : ℝ) (y : E) :
    advancedSolution F f μ t y =
      ∫ s in Set.Ioi t, sineEvolution F (s - t) μ (slice F f s) y := by
  unfold advancedSolution
  rw [solution_eq_integral F _ hμ]
  have h := integral_comp_neg_Iic (-t) (fun s => sineEvolution F (s - t) μ (slice F f s) y)
  rw [neg_neg] at h
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Iic fun σ _ => ?_
  have : slice F (reflect F f) σ = slice F f (-σ) := by ext x; rfl
  rw [this, show -t - σ = -σ - t by ring]
end

section
variable {D : Type} [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D]
    [MeasurableSpace D] [BorelSpace D]

/-- **Advanced response at a point.** The advanced solution at the point `(t, y)` is the integral
over the later source times of the pairing of the propagated Dirac distribution at `y` with the
slice of the source. By transposition this is the retarded response of a point source. -/
lemma advancedSolution_eq_dirac {μ : ℝ} (hμ : 0 ≤ μ) (f : 𝓓((⊤ : Opens (ℝ × D)), ℂ))
    (t : ℝ) (y : D) :
    advancedSolution ℂ f μ t y =
      ∫ s in Set.Ioi t, sineEvolutionTempered ℂ (s - t) μ (TemperedDistribution.delta y)
        (slice ℂ f s) := by
  rw [advancedSolution_eq_integral ℂ f hμ]
  exact setIntegral_congr_fun measurableSet_Ioi fun s _ =>
    sineEvolution_apply_eq_delta hμ (s - t) (slice ℂ f s) y
end

end KleinGordon
