/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Regular

/-!
# Continuous functions are a.e. strongly measurable for inner regular measures

Mathlib's `ContinuousOn.aestronglyMeasurable` and `Continuous.aestronglyMeasurable` read almost
everywhere strong measurability of a continuous function off second countability of its source or
target.

## i. Overview

Mathlib's `ContinuousOn.aestronglyMeasurable` and `Continuous.aestronglyMeasurable` read almost
everywhere strong measurability of a continuous function off second countability of its source or
target. This file gives the alternative source of separability: inner regularity of the measure.
If `μ` is inner regular with respect to compact sets on measurable sets of finite measure
(`MeasureTheory.Measure.InnerRegularCompactLTTop`), as every regular measure is (for instance the
Haar measure `MeasureTheory.Measure.addHaar` of a locally compact group), then up to a null set each
such set is a countable union of compact sets, whose images under a continuous function are
separable.

The main application is to integrands `f x • g x` with `f` integrable and `g` continuous, such as
the orbits `g ↦ f g • π g v` integrated in the integrated form of a strongly continuous group
representation. On a locally compact group that is not σ-compact a Haar measure is not σ-finite,
and a continuous function need not be a.e. strongly measurable on the whole group; but an
integrable `f` lives on a σ-finite set, and there the inner regular case applies.

## ii. Key results

* `ContinuousOn.aestronglyMeasurable_of_measure_ne_top`: a function continuous on a measurable set
  of finite measure is a.e. strongly measurable for the restriction of `μ` to that set.
* `Continuous.aestronglyMeasurable_of_sigmaFinite`: a continuous function is a.e. strongly
  measurable for a σ-finite inner regular measure.
* `MeasureTheory.AEFinStronglyMeasurable.aestronglyMeasurable_smul`: the product `f • g` of an
  a.e. finitely strongly measurable `f` (for instance an integrable one) and a continuous `g` is
  a.e. strongly measurable.

## iii. Table of contents

- A. Development

## iv. References

* Standard material; the statements and proofs are original to this formalization.
-/

public section

/-! ## A. Development -/

open MeasureTheory Set TopologicalSpace
open scoped ENNReal

variable {α β : Type*} [TopologicalSpace α] [MeasurableSpace α] [R1Space α] [BorelSpace α]
  [TopologicalSpace β] [PseudoMetrizableSpace β] {μ : Measure α} [μ.InnerRegularCompactLTTop]

/-- For a measure that is inner regular with respect to compact sets on sets of finite measure, a
function continuous on a measurable set `s` of finite measure is a.e. strongly measurable for the
restriction of the measure to `s`. -/
lemma ContinuousOn.aestronglyMeasurable_of_measure_ne_top {f : α → β} {s : Set α}
    (hf : ContinuousOn f s) (hs : MeasurableSet s) (hμs : μ s ≠ ∞) :
    AEStronglyMeasurable f (μ.restrict s) := by
  -- Exhaust `s` up to a null set by countably many closed compact subsets.
  choose K hKs hKc hKcl hμK using fun n : ℕ ↦
    hs.exists_isCompact_isClosed_sdiff_lt hμs (ε := (n + 1 : ℝ≥0∞)⁻¹) (by simp)
  have hnull : μ (s \ ⋃ n, K n) = 0 := by
    refine nonpos_iff_eq_zero.1 (ge_of_tendsto' ENNReal.tendsto_inv_nat_nhds_zero fun n ↦ ?_)
    calc μ (s \ ⋃ n, K n) ≤ μ (s \ K n) :=
        measure_mono (sdiff_subset_sdiff_right (subset_iUnion K n))
      _ ≤ (n + 1 : ℝ≥0∞)⁻¹ := (hμK n).le
      _ ≤ (n : ℝ≥0∞)⁻¹ := ENNReal.inv_le_inv.2 le_self_add
  have hae : (⋃ n, K n : Set α) =ᵐ[μ] s :=
    (iUnion_subset hKs).eventuallyLE.antisymm (ae_le_set.2 hnull)
  rw [← Measure.restrict_congr_set hae, aestronglyMeasurable_iUnion_iff]
  exact fun n ↦ (hf.mono (hKs n)).aestronglyMeasurable_of_isCompact (hKc n) (hKcl n).measurableSet

/-- A continuous function is a.e. strongly measurable for a σ-finite measure that is inner regular
with respect to compact sets on sets of finite measure. Compare `Continuous.aestronglyMeasurable`,
which asks for second countability of the source or the target instead. -/
lemma Continuous.aestronglyMeasurable_of_sigmaFinite [SigmaFinite μ] {f : α → β}
    (hf : Continuous f) : AEStronglyMeasurable f μ := by
  rw [← Measure.restrict_univ (μ := μ), ← iUnion_spanningSets μ, aestronglyMeasurable_iUnion_iff]
  exact fun n ↦ hf.continuousOn.aestronglyMeasurable_of_measure_ne_top
    (measurableSet_spanningSets μ n) (measure_spanningSets_lt_top μ n).ne

/-- The product of an a.e. finitely strongly measurable function `f`, for instance an integrable
one, and a continuous function `g` is a.e. strongly measurable, for a measure that is inner regular
with respect to compact sets on sets of finite measure. No σ-finiteness of the measure and no
second countability is needed: `f` vanishes outside a σ-finite set, on which `g` is a.e. strongly
measurable by `Continuous.aestronglyMeasurable_of_sigmaFinite`. -/
lemma MeasureTheory.AEFinStronglyMeasurable.aestronglyMeasurable_smul {𝕜 : Type*}
    [TopologicalSpace 𝕜] [T2Space 𝕜] [Zero 𝕜] [Zero β] [SMulWithZero 𝕜 β] [ContinuousSMul 𝕜 β]
    {f : α → 𝕜} (hf : AEFinStronglyMeasurable f μ) {g : α → β} (hg : Continuous g) :
    AEStronglyMeasurable (fun x ↦ f x • g x) μ := by
  rw [← Measure.restrict_univ (μ := μ), ← union_compl_self hf.sigmaFiniteSet,
    aestronglyMeasurable_union_iff]
  refine ⟨(AEStronglyMeasurable.restrict ⟨hf.mk f, hf.finStronglyMeasurable_mk.stronglyMeasurable,
      hf.ae_eq_mk⟩).smul hg.aestronglyMeasurable_of_sigmaFinite,
    (aestronglyMeasurable_const (b := (0 : β))).congr ?_⟩
  filter_upwards [hf.ae_eq_zero_compl] with x hx
  simp [hx]
