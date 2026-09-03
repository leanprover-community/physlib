/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Normalized Haar measure on compact groups

This file normalizes Mathlib's Haar measure on a compact topological group to a probability
measure, and records its left, right, and inversion invariance.

The Layer 0 design follows the [compact-groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/roadmap/representation-theory/TauCetiRoadmap/RepresentationTheory/CompactGroups/README.md)
and its accompanying `Suggested.lean`.

Since `haarProb` is a Haar measure and a probability measure, Mathlib's generic API applies to
it directly: `MeasureTheory.Measure.isHaarMeasure_eq_of_isProbabilityMeasure` identifies it with
any other Haar probability measure, and `MeasureTheory.integral_mul_left_eq_self`,
`MeasureTheory.integral_mul_right_eq_self` and `MeasureTheory.integral_inv_eq_self` give the
translation and inversion identities used for averaging representations.
-/

public section

open MeasureTheory Set

namespace TauCeti

section LocallyCompactGroup

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-- Haar measure of a nonempty locally compact group has nonzero total mass. -/
theorem haar_univ_ne_zero : (Measure.haar : Measure G) univ ≠ 0 :=
  (Measure.measure_pos_of_nonempty_interior (μ := Measure.haar) (by simp)).ne'

/-- Every probability Haar measure on a locally compact group is right-invariant. -/
theorem isMulRightInvariant_of_isHaarMeasure_of_isProbabilityMeasure (μ : Measure G)
    [μ.IsHaarMeasure] [IsProbabilityMeasure μ] : μ.IsMulRightInvariant where
  map_mul_right_eq_self g := by
    have : (Measure.map (· * g) μ).IsHaarMeasure :=
      Measure.isHaarMeasure_map_mul_right μ g
    have : IsProbabilityMeasure (Measure.map (· * g) μ) :=
      Measure.isProbabilityMeasure_map (measurable_mul_const g).aemeasurable
    exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _

/-- Every probability Haar measure on a locally compact group is invariant under inversion. -/
theorem isInvInvariant_of_isHaarMeasure_of_isProbabilityMeasure (μ : Measure G)
    [μ.IsHaarMeasure] [IsProbabilityMeasure μ] : μ.IsInvInvariant := by
  have : μ.IsMulRightInvariant :=
    isMulRightInvariant_of_isHaarMeasure_of_isProbabilityMeasure (G := G) μ
  constructor
  let : μ.inv.IsHaarMeasure := {
    toIsFiniteMeasureOnCompacts := inferInstance
    toIsMulLeftInvariant := inferInstance
    toIsOpenPosMeasure := inferInstance }
  let : IsProbabilityMeasure μ.inv := by
    rw [Measure.inv_def]
    exact Measure.isProbabilityMeasure_map measurable_inv.aemeasurable
  exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _

end LocallyCompactGroup

section CompactGroup

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-- Haar measure of a compact group has finite total mass. -/
theorem haar_univ_lt_top : (Measure.haar : Measure G) univ < ⊤ :=
  measure_lt_top _ _

private noncomputable def haarFinite : FiniteMeasure G :=
  ⟨Measure.haar, inferInstance⟩

/-- The finite measure used to normalize Haar measure has underlying measure `Measure.haar`. -/
private theorem haarFinite_toMeasure : (haarFinite G : Measure G) = Measure.haar := by
  ext s hs
  rfl

private theorem haarFinite_ne_zero : haarFinite G ≠ 0 := by
  rw [← FiniteMeasure.mass_nonzero_iff]
  apply ENNReal.coe_ne_zero.mp
  rw [FiniteMeasure.ennreal_mass, haarFinite_toMeasure]
  exact haar_univ_ne_zero G

/-- Haar probability measure on a compact topological group. -/
noncomputable def haarProb : Measure G :=
  (haarFinite G).normalize

/-- The definition of normalized Haar measure as a rescaling of Mathlib's Haar measure. -/
theorem haarProb_def :
    haarProb G = ((Measure.haar : Measure G) univ)⁻¹ • Measure.haar :=
  by
    rw [haarProb,
      FiniteMeasure.toMeasure_normalize_eq_of_nonzero (haarFinite G) (haarFinite_ne_zero G)]
    rw [← haarFinite_toMeasure]
    rw [← FiniteMeasure.ennreal_mass, ← ENNReal.coe_inv]
    · rfl
    · exact (FiniteMeasure.mass_nonzero_iff (haarFinite G)).mpr (haarFinite_ne_zero G)

instance isProbabilityMeasure_haarProb : IsProbabilityMeasure (haarProb G) := by
  exact (haarFinite G).normalize.property

/-- Normalized Haar measure has total mass one.

Not a `simp` lemma: `simp` already closes this goal from the `IsProbabilityMeasure` instance
via `MeasureTheory.measure_univ`. -/
theorem haarProb_apply_univ : haarProb G univ = 1 :=
  measure_univ

instance isMulLeftInvariant_haarProb : (haarProb G).IsMulLeftInvariant := by
  rw [haarProb_def]
  infer_instance

instance isHaarMeasure_haarProb : (haarProb G).IsHaarMeasure := by
  rw [haarProb_def]
  exact Measure.IsHaarMeasure.smul Measure.haar
    (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _))
    (ENNReal.inv_ne_top.mpr (NeZero.ne _))

/-- Normalized Haar measure is invariant under right multiplication. -/
instance isMulRightInvariant_haarProb : (haarProb G).IsMulRightInvariant :=
  isMulRightInvariant_of_isHaarMeasure_of_isProbabilityMeasure (G := G) _

/-- Normalized Haar measure is invariant under inversion. -/
instance isInvInvariant_haarProb : (haarProb G).IsInvInvariant :=
  isInvInvariant_of_isHaarMeasure_of_isProbabilityMeasure (G := G) _

/-- A probability Haar measure on a compact group is the normalized Haar measure. -/
theorem eq_haarProb_of_isHaarMeasure_of_isProbabilityMeasure (μ : Measure G)
    [μ.IsHaarMeasure] [IsProbabilityMeasure μ] : μ = haarProb G :=
  Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _

end CompactGroup

end TauCeti
