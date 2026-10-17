/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import PhyslibAlpha.Mathematics.TauCeti.Analysis.Fourier.Pontryagin.Measure
public import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Continuity of the Fourier–Stieltjes transform on a Pontryagin dual

The Fourier–Stieltjes transform of a tight finite positive measure on the Pontryagin dual is
continuous on the original locally compact group.

## i. Overview

The Fourier–Stieltjes transform of a tight finite positive measure on the Pontryagin dual is
continuous on the original locally compact group. Together with its positive-definiteness,
this supplies the measure-to-function direction of Bochner representation on locally compact
abelian groups for regular measures. A compact set carries almost all of the measure; character
evaluation is uniformly continuous there near each fixed group element, while the complement
contributes at most its small mass.

This is the standard compact truncation argument for Fourier–Stieltjes transforms; see
G. B. Folland, *A Course in Abstract Harmonic Analysis*, Chapter 4.

## ii. Key results

This file proves the statement described in the overview.

## iii. Table of contents

- A. Development

## iv. References

* Standard material; the statements and proofs are original to this formalization.
-/

public section

/-! ## A. Development -/

open MeasureTheory

namespace TauCeti

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [LocallyCompactSpace G]
  [MeasurableSpace (PontryaginDual (Multiplicative G))]
  [OpensMeasurableSpace (PontryaginDual (Multiplicative G))]

/-- The transform of a tight finite measure on the Pontryagin dual is continuous. Tightness is
automatic for finite Radon measures and is the regularity needed when the dual is not metrizable. -/
lemma _root_.MeasureTheory.FiniteMeasure.continuous_pontryaginMeasureTransform
    (μ : FiniteMeasure (PontryaginDual (Multiplicative G)))
    (hμ : IsTightMeasureSet {μ.toMeasure}) :
    Continuous μ.pontryaginMeasureTransform := by
  rw [continuous_iff_continuousAt]
  intro g
  rw [ContinuousAt]
  refine Metric.nhds_basis_ball.tendsto_right_iff.mpr ?_
  intro ε hε
  let C := μ.toMeasure.real Set.univ + 1
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨K, hK, hKmass⟩ :=
    isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp hμ
      (ENNReal.ofReal (ε / 8)) (ENNReal.ofReal_pos.mpr (by positivity))
  have hKmeas : MeasurableSet K := hK.isClosed.measurableSet
  have htail : μ.toMeasure.real Kᶜ ≤ ε / 8 := by
    have hle := hKmass μ.toMeasure (Set.mem_singleton _)
    -- Real measure is the finite ENNReal measure converted to a real number.
    change (μ.toMeasure Kᶜ).toReal ≤ ε / 8
    have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
    rw [ENNReal.toReal_ofReal (by positivity)] at ht
    exact ht
  let δ := ε / (4 * C)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let U : Set (G × PontryaginDual (Multiplicative G)) :=
    {p | ‖(p.2 (Multiplicative.ofAdd p.1) : ℂ) -
      (p.2 (Multiplicative.ofAdd g) : ℂ)‖ < δ}
  have hUopen : IsOpen U := by
    dsimp [U]
    apply isOpen_lt
    · apply Continuous.norm
      apply Continuous.sub
      · have h : Continuous (fun p : PontryaginDual (Multiplicative G) × Multiplicative G =>
            (p.1 p.2 : Circle)) := by
            -- PontryaginDual is the continuous-monoid-hom type with its compact-open topology.
            change Continuous (fun p : (Multiplicative G →ₜ* Circle) × Multiplicative G => p.1 p.2)
            exact continuous_eval
        exact (LipschitzWith.subtype_val (Submonoid.unitSphere ℂ).carrier).continuous.comp
          (h.comp (continuous_snd.prodMk
            (continuous_ofAdd.comp continuous_fst)))
      · exact (PontryaginDual.continuous_coe_eval_const (Multiplicative.ofAdd g)).comp
          continuous_snd
    · exact continuous_const
  have hUcontains : ({g} : Set G) ×ˢ K ⊆ U := by
    rintro ⟨x, χ⟩ ⟨hx, -⟩
    simp only [Set.mem_singleton_iff] at hx
    subst x
    simpa [U] using hδ
  obtain ⟨N, V, hNopen, _, hgN, hKV, hNU⟩ :=
    generalized_tube_lemma (isCompact_singleton (x := g)) hK hUopen hUcontains
  refine Filter.mem_of_superset (hNopen.mem_nhds (hgN (Set.mem_singleton g))) ?_
  intro x hx
  -- The ball basis expresses continuity through the distance between transform values.
  change dist (μ.pontryaginMeasureTransform x) (μ.pontryaginMeasureTransform g) < ε
  rw [dist_eq_norm]
  have hsmall (χ : PontryaginDual (Multiplicative G)) (hχ : χ ∈ K) :
      ‖(χ (Multiplicative.ofAdd x) : ℂ) -
        (χ (Multiplicative.ofAdd g) : ℂ)‖ ≤ δ := by
    have hlt : ‖(χ (Multiplicative.ofAdd x) : ℂ) -
        (χ (Multiplicative.ofAdd g) : ℂ)‖ < δ := by
      simpa [U] using hNU (show (x, χ) ∈ N ×ˢ V from ⟨hx, hKV hχ⟩)
    exact hlt.le
  have hint (y : G) : Integrable
      (fun χ : PontryaginDual (Multiplicative G) =>
        (χ (Multiplicative.ofAdd y) : ℂ)) μ.toMeasure :=
    PontryaginDual.integrable_coe_eval (Multiplicative.ofAdd y)
  have hcenter :
      ‖(∫ χ in K, (χ (Multiplicative.ofAdd x) : ℂ) ∂μ.toMeasure) -
        (∫ χ in K, (χ (Multiplicative.ofAdd g) : ℂ) ∂μ.toMeasure)‖ ≤
          δ * μ.toMeasure.real K := by
    rw [← integral_sub (hint x).integrableOn (hint g).integrableOn]
    exact norm_setIntegral_le_of_norm_le_const (measure_lt_top μ.toMeasure K)
      (fun χ hχ => hsmall χ hχ)
  have htail' (y : G) :
      ‖(∫ χ, (χ (Multiplicative.ofAdd y) : ℂ) ∂μ.toMeasure) -
        (∫ χ in K, (χ (Multiplicative.ofAdd y) : ℂ) ∂μ.toMeasure)‖ ≤
          μ.toMeasure.real Kᶜ := by
    simpa using norm_integral_sub_setIntegral_le
      (μ := μ.toMeasure) (C := 1)
      (f := fun χ : PontryaginDual (Multiplicative G) =>
        (χ (Multiplicative.ofAdd y) : ℂ))
      (Filter.Eventually.of_forall fun χ => by simp) hKmeas (hint y)
  have hmass : μ.toMeasure.real K ≤ C := by
    exact (measureReal_mono (μ := μ.toMeasure) (Set.subset_univ K)).trans
      (by dsimp [C]; linarith)
  have hcenter' : δ * μ.toMeasure.real K ≤ ε / 4 := by
    calc
      δ * μ.toMeasure.real K ≤ δ * C := mul_le_mul_of_nonneg_left hmass hδ.le
      _ = ε / 4 := by dsimp [δ]; field_simp
  let A : ℂ := ∫ χ, (χ (Multiplicative.ofAdd x) : ℂ) ∂μ.toMeasure
  let B : ℂ := ∫ χ in K, (χ (Multiplicative.ofAdd x) : ℂ) ∂μ.toMeasure
  let D : ℂ := ∫ χ, (χ (Multiplicative.ofAdd g) : ℂ) ∂μ.toMeasure
  let E : ℂ := ∫ χ in K, (χ (Multiplicative.ofAdd g) : ℂ) ∂μ.toMeasure
  rw [FiniteMeasure.pontryaginMeasureTransform_apply,
    FiniteMeasure.pontryaginMeasureTransform_apply]
  -- Name the four integrals to make the two triangle inequalities transparent.
  change ‖A - D‖ < ε
  calc
    ‖A - D‖ ≤ ‖A - B‖ + ‖B - E‖ + ‖E - D‖ := by
      calc
        _ ≤ ‖A - B‖ + ‖B - D‖ := norm_sub_le_norm_sub_add_norm_sub A B D
        _ ≤ _ := by
          simpa only [add_assoc] using
            add_le_add_right (norm_sub_le_norm_sub_add_norm_sub B E D) ‖A - B‖
    _ ≤ μ.toMeasure.real Kᶜ + δ * μ.toMeasure.real K +
          μ.toMeasure.real Kᶜ := by
          exact add_le_add (add_le_add (htail' x) hcenter)
            (by simpa [norm_sub_rev] using htail' g)
    _ < ε := by linarith

end TauCeti

end
