/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.KleinGordon.Solution
public import Mathlib.Analysis.Fourier.Inversion

/-!

# The spatial Fourier transform of the retarded solution

The retarded solution at time `t` has the spatial Fourier transform given by the Duhamel integral
of the sine multiplier.

## i. Overview

For a source `f` of compact support the slice of the retarded solution at time `t` is a Schwartz
function in space. Its spatial Fourier transform at the frequency `ξ` is the integral over
earlier times `s` of the sine multiplier `sin(ω (t - s)) / ω` times the Fourier transform of the
source slice at time `s`. Outside the time support of the source the transform obeys the free
oscillator evolution of its value and velocity at the last time of the support.

## ii. Key results

- `fourier_solutionSlice` : the Fourier transform of the retarded slice.

## iii. Table of contents

- A. The Fourier transform of the retarded slice

## iv. References

None.

## A. The Fourier transform of the retarded slice

- `fourier_solutionSlice` : the Fourier transform of the retarded slice.
-/

@[expose] public section

noncomputable section

open scoped FourierTransform Distributions
open MeasureTheory TimeSlice Duhamel SincPropagator

universe u

namespace KleinGordon

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (F : Type u) [NormedAddCommGroup F] [NormedSpace ℂ F]
  [CompleteSpace F] (f : 𝓓((⊤ : TopologicalSpace.Opens (ℝ × E)), F))

/-- The Fourier transform of the retarded slice, when the source vanishes before the time `a`. -/
lemma fourier_solutionSlice_of_le {μ : ℝ} (hμ : 0 ≤ μ) {a : ℝ}
    (ha : ∀ s ≤ a, s ∉ Prod.fst '' tsupport f) {t : ℝ} (hat : a ≤ t) (ξ : E) :
    𝓕 (solutionSlice F f hμ t) ξ = freqSolution F f μ a ξ t := by
  set h : E → F := fun ξ => freqSolution F f μ a ξ t with hh
  have hcont : Continuous h := continuous_freqSolution_xi F f μ a t
  have hint : Integrable h volume := by
    have := integrable_norm_pow_mul_freqSolution F f μ a t (n := 0) (by norm_num)
    exact (integrable_norm_iff hcont.aestronglyMeasurable).mp (by simpa using this)
  have hg : ⇑(solutionSlice F f hμ t) = 𝓕⁻ h := by
    funext x
    rw [solutionSlice_apply, solution_eq F f ha hat x, Real.fourierInv_eq]
    rfl
  have hF : 𝓕 (fun x => h (-x)) = ⇑(solutionSlice F f hμ t) := by
    rw [hg, Real.fourierInv_eq_fourier_comp_neg]
  have hf₁ : Integrable (fun x => h (-x)) volume := hint.comp_neg
  have hS : Integrable (𝓕 fun x => h (-x)) volume := by
    rw [hF]; exact (solutionSlice F f hμ t).integrable
  have hinv := hf₁.fourierInv_fourier_eq hS (v := -ξ) (hcont.comp continuous_neg).continuousAt
  rw [hF] at hinv
  rw [SchwartzMap.fourier_coe, ← neg_neg ξ, ← Real.fourierInv_eq_fourier_neg, hinv]

/-- The Fourier transform of the retarded slice at time `t` is the integral over earlier times of
the sine multiplier times the Fourier transform of the source slice. -/
lemma fourier_solutionSlice {μ : ℝ} (hμ : 0 ≤ μ) (t : ℝ) (ξ : E) :
    𝓕 (solutionSlice F f hμ t) ξ =
      ∫ s in Set.Iic t, multiplier (t - s) μ ξ • 𝓕 (slice F f s) ξ := by
  obtain ⟨a, ha⟩ := exists_timeBound F f
  have ha' : ∀ s ≤ min a t, s ∉ Prod.fst '' tsupport f := fun s hs =>
    ha s (hs.trans (min_le_left _ _))
  have hat : min a t ≤ t := min_le_right _ _
  rw [fourier_solutionSlice_of_le F f hμ ha' hat, freqSolution,
    intervalIntegral.integral_of_le hat]
  refine (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Iic
    Set.Ioc_subset_Iic_self ?_).symm
  intro s hs
  have hsmin : s ≤ min a t := by
    by_contra h
    exact hs.2 ⟨not_le.mp h, hs.1⟩
  simp [sourceHat, slice_eq_zero_of_notMem F f (ha' s hsmin)]

omit [CompleteSpace F] in
/-- After the last time of the source the Fourier mode of the retarded solution is the free
oscillator evolution of its value and velocity at that time. -/
lemma freqSolution_cauchy {μ : ℝ} {a T t : ℝ} (hT : ∀ s ≥ T, s ∉ Prod.fst '' tsupport f)
    (hTt : T ≤ t) (ξ : E) :
    freqSolution F f μ a ξ t =
      (Real.cos (dispersion μ ξ * (t - T)) : ℂ) • freqSolution F f μ a ξ T +
        (Real.sincPropagator (t - T) (dispersion μ ξ) : ℂ) • freqSolution1 F f μ a ξ T := by
  set ω := dispersion μ ξ with hω
  have hsh : Continuous (sourceHat F f ξ) := continuous_sourceHat F f ξ
  have hM : ∀ τ, Continuous fun s => multiplier (τ - s) μ ξ := fun τ =>
    (continuous_multiplier_uncurry (E := E) μ).comp
      ((continuous_const.sub continuous_id).prodMk continuous_const)
  have hC : ∀ τ, Continuous fun s : ℝ => Real.cos (ω * (τ - s)) := fun τ => by fun_prop
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (f := fun s => multiplier (t - s) μ ξ • sourceHat F f ξ s) (a := a) (b := T) (c := t)
    (((hM t).smul hsh).intervalIntegrable (μ := MeasureTheory.volume) _ _)
    (((hM t).smul hsh).intervalIntegrable (μ := MeasureTheory.volume) _ _)
  have hzero : ∫ s in T..t, multiplier (t - s) μ ξ • sourceHat F f ξ s = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : F)) ?_]
    · simp
    · intro s hs
      rw [Set.uIcc_of_le hTt] at hs
      simp [sourceHat, slice_eq_zero_of_notMem F f (hT s hs.1)]
  have hpt : ∀ s, multiplier (t - s) μ ξ • sourceHat F f ξ s =
      (Real.cos (ω * (t - T)) : ℂ) • (multiplier (T - s) μ ξ • sourceHat F f ξ s) +
        (Real.sincPropagator (t - T) ω : ℂ) • (Real.cos (ω * (T - s)) • sourceHat F f ξ s) := by
    intro s
    have h : multiplier (t - s) μ ξ = (Real.cos (ω * (t - T)) : ℂ) * multiplier (T - s) μ ξ +
        (Real.sincPropagator (t - T) ω : ℂ) * (Real.cos (ω * (T - s)) : ℂ) := by
      simp only [multiplier]
      rw [show t - s = (t - T) + (T - s) by ring, Real.sincPropagator_add]
      push_cast
      ring
    rw [h, add_smul, mul_smul, mul_smul]
    simp only [Complex.coe_smul]
  have h1 : IntervalIntegrable (fun s => multiplier (T - s) μ ξ • sourceHat F f ξ s)
      MeasureTheory.volume a T := ((hM T).smul hsh).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun s => Real.cos (ω * (T - s)) • sourceHat F f ξ s)
      MeasureTheory.volume a T := ((hC T).smul hsh).intervalIntegrable _ _
  unfold freqSolution freqSolution1 Real.duhamelOscCos
  rw [← hsplit, hzero, add_zero]
  simp_rw [hpt]
  have i1 : IntervalIntegrable (fun s => (Real.cos (ω * (t - T)) : ℂ) •
      (multiplier (T - s) μ ξ • sourceHat F f ξ s)) MeasureTheory.volume a T := h1.smul _
  have i2 : IntervalIntegrable (fun s => (Real.sincPropagator (t - T) ω : ℂ) •
      (Real.cos (ω * (T - s)) • sourceHat F f ξ s)) MeasureTheory.volume a T := h2.smul _
  rw [intervalIntegral.integral_add i1 i2, intervalIntegral.integral_smul,
    intervalIntegral.integral_smul]

end

end KleinGordon
