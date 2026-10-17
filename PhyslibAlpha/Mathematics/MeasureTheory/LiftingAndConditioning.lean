/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import PhyslibAlpha.Mathematics.MeasureTheory.PositiveFunctionalIntegral
public import PhyslibAlpha.Mathematics.MeasureTheory.IntegrationFunctional
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
public import Mathlib.MeasureTheory.Measure.Prokhorov

/-!
# Lifting, averaging and conditioning probability measures

Lifting, averaging, conditioning and replacing parts of probability measures.

## i. Overview

This file collects operations on probability measures used in Choquet's theorem. A probability
measure on the compact range of a continuous map is the image of a probability measure on its
source. The images of one measure under two maps can be averaged. A measure can be conditioned on an
event of positive probability. Finally, the part of a measure on an event can be handed to another
measure.

## ii. Key results

- `ProbabilityMeasure.exists_map_eq_of_continuous_of_compl_range_null` proves that a probability
  measure on the range of a continuous map lifts to its source.
- `ProbabilityMeasure.averageMap` is the average of two images of a measure.
- `ProbabilityMeasure.condition` conditions a measure on an event.
- `ProbabilityMeasure.replacePart` replaces the part of a measure on an event.

## iii. Table of contents

- A. Lifting through a compact continuous map
- B. Averaging two pushforwards
- C. Conditioning and replacing part of a measure

## iv. References

* None.

-/

@[expose] public section

open MeasureTheory Filter Topology Set

namespace ProbabilityMeasure

/-!

## A. Lifting through a compact continuous map

-/

section CompactLift

variable {X Y : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [TopologicalSpace Y] [CompactSpace Y]
  [TopologicalSpace.MetrizableSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-- A probability measure charging only the range of a continuous map from a compact space lifts
through that map: integration against it is a positive functional on continuous functions on the
domain, which extends and is represented by a measure. -/
lemma exists_map_eq_of_continuous_of_compl_range_null (q : X → Y) (hq : Continuous q)
    (mu : ProbabilityMeasure Y) (hmu : (mu : Measure Y) (Set.range q)ᶜ = 0) :
    ∃ nu : ProbabilityMeasure X, nu.map q = mu := by
  let T : C(Y, ℝ) →ₗ[ℝ] C(X, ℝ) := ⟨⟨fun f => f.comp ⟨q, hq⟩, fun _ _ => rfl⟩, fun _ _ => rfl⟩
  obtain ⟨ν, -, hν, hint⟩ := exists_regular_probabilityMeasure_integral_eq T
    (integralCLM (mu : Measure Y)).toLinearMap
    (fun f hf => integral_nonneg_of_ae ((ae_iff.2 hmu).mono fun y ⟨x, hx⟩ => hx ▸ hf x))
    (one := 1) rfl (by simp)
  refine ⟨⟨ν, hν⟩, ProbabilityMeasure.toMeasure_injective
    (ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_)⟩
  change ∫ y, f y ∂(ν.map q) = _
  rw [integral_map hq.aemeasurable f.continuous.aestronglyMeasurable]
  exact hint f.toContinuousMap

end CompactLift

section AverageMap

/-!

## B. Averaging two pushforwards

-/

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-- The average of the two pushforwards of a probability measure. -/
noncomputable def averageMap (rho : ProbabilityMeasure A) (f g : A → B)
    (hf : AEMeasurable f rho) (hg : AEMeasurable g rho) : ProbabilityMeasure B :=
  ⟨ENNReal.ofReal ((1 : ℝ) / 2) • (rho.map f : Measure B) +
    ENNReal.ofReal ((1 : ℝ) / 2) • (rho.map g : Measure B), by
    constructor
    rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
      ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_map,
      Measure.map_apply_of_aemeasurable hf MeasurableSet.univ,
      Measure.map_apply_of_aemeasurable hg MeasurableSet.univ]
    simp only [Set.preimage_univ, MeasureTheory.measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num⟩

lemma integral_averageMap {rho : ProbabilityMeasure A} {f g : A → B}
    (hf : AEMeasurable f rho) (hg : AEMeasurable g rho) {u : B → ℝ}
    (hu : Integrable u (rho.map f))
    (hv : Integrable u (rho.map g)) :
    ∫ x, u x ∂(averageMap rho f g hf hg : Measure B) =
      ((1 : ℝ) / 2) * (∫ x, u (f x) ∂(rho : Measure A)) +
        ((1 : ℝ) / 2) * (∫ x, u (g x) ∂(rho : Measure A)) := by
  change ∫ x, u x ∂(ENNReal.ofReal ((1 : ℝ) / 2) • (rho.map f : Measure B) +
      ENNReal.ofReal ((1 : ℝ) / 2) • (rho.map g : Measure B)) = _
  rw [integral_add_measure (hu.smul_measure ENNReal.ofReal_ne_top)
      (hv.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure,
    ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_map,
    integral_map hf hu.1, integral_map hg hv.1, ENNReal.toReal_ofReal (by norm_num)]
  ring

end AverageMap

section ReplacePart

/-!

## C. Conditioning and replacing part of a measure

-/

variable {B : Type*} [MeasurableSpace B]

/-- The conditional law of a probability measure on a positive-measure event. -/
noncomputable def condition (mu : ProbabilityMeasure B) (S : Set B)
    (hS : (mu : Measure B) S ≠ 0) : ProbabilityMeasure B :=
  ⟨ProbabilityTheory.cond (mu : Measure B) S,
    ProbabilityTheory.cond_isProbabilityMeasure hS⟩

lemma condition_compl_apply (mu : ProbabilityMeasure B) {S : Set B}
    (hSm : MeasurableSet S) (hS : (mu : Measure B) S ≠ 0) :
    (condition mu S hS : Measure B) Sᶜ = 0 := by
  change ProbabilityTheory.cond (mu : Measure B) S Sᶜ = 0
  rw [ProbabilityTheory.cond_apply hSm]
  simp

lemma measure_smul_condition_eq_restrict (mu : ProbabilityMeasure B) {S : Set B}
    (hSm : MeasurableSet S) (hS : (mu : Measure B) S ≠ 0) :
    (mu : Measure B) S • (condition mu S hS : Measure B) = (mu : Measure B).restrict S := by
  ext T hT
  rw [Measure.smul_apply, Measure.restrict_apply hT]
  change (mu : Measure B) S * ProbabilityTheory.cond (mu : Measure B) S T = _
  rw [mul_comm, ProbabilityTheory.cond_mul_eq_inter hSm, Set.inter_comm]

/-- Replace the mass of `mu` on `S` by the same amount of another probability measure. -/
noncomputable def replacePart (mu eta : ProbabilityMeasure B) (S : Set B)
    (hS : MeasurableSet S) : ProbabilityMeasure B :=
  ⟨(mu : Measure B).restrict Sᶜ + (mu : Measure B) S • (eta : Measure B), by
    constructor
    rw [Measure.add_apply, Measure.restrict_apply MeasurableSet.univ,
      Measure.smul_apply, Set.univ_inter, MeasureTheory.measure_univ]
    simp only [smul_eq_mul, mul_one]
    simpa [add_comm] using prob_add_prob_compl (μ := (mu : Measure B)) hS⟩

lemma replacePart_toMeasure (mu eta : ProbabilityMeasure B) (S : Set B)
    (hS : MeasurableSet S) :
    (replacePart mu eta S hS : Measure B) =
      (mu : Measure B).restrict Sᶜ + (mu : Measure B) S • (eta : Measure B) := rfl

/-- Integrating against `mu` splits into the part off `S` plus the mass of `S` times the
conditional integral on `S`. -/
lemma integral_eq_restrict_compl_add_condition (mu : ProbabilityMeasure B) {S : Set B}
    (hS : MeasurableSet S) (hpos : (mu : Measure B) S ≠ 0) {f : B → ℝ}
    (hf : Integrable f (mu : Measure B)) :
    ∫ x, f x ∂(mu : Measure B) = ∫ x, f x ∂((mu : Measure B).restrict Sᶜ) +
      ((mu : Measure B) S).toReal * ∫ x, f x ∂(condition mu S hpos : Measure B) := by
  rw [← smul_eq_mul, ← integral_smul_measure, measure_smul_condition_eq_restrict mu hS hpos,
    ← integral_add_measure (hf.mono_measure Measure.restrict_le_self)
      (hf.mono_measure Measure.restrict_le_self), Measure.restrict_compl_add_restrict hS]

lemma integral_replacePart (mu eta : ProbabilityMeasure B) (S : Set B) (hS : MeasurableSet S)
    {f : B → ℝ} (hmu : Integrable f (mu : Measure B)) (heta : Integrable f (eta : Measure B)) :
    ∫ x, f x ∂(replacePart mu eta S hS : Measure B) = ∫ x, f x ∂((mu : Measure B).restrict Sᶜ) +
      ((mu : Measure B) S).toReal * ∫ x, f x ∂(eta : Measure B) := by
  rw [replacePart_toMeasure, integral_add_measure (hmu.mono_measure Measure.restrict_le_self)
    (heta.smul_measure (measure_ne_top _ _)), integral_smul_measure, smul_eq_mul]

end ReplacePart

end ProbabilityMeasure
