/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.MeasureTheory.Measure.Regular

/-!
# Regular measures

Inner regularity and regularity pass to smaller measures, continuous images and subsets.

## i. Overview

A measure is regular when the measure of a set is approximated by compact sets from inside and by
open sets from outside. For finite measures on a Hausdorff space the inner approximation is enough.
Inner regularity passes to smaller measures, along continuous maps and to measurable subsets, and so
regularity does too.

## ii. Key results

- `MeasureTheory.Measure.InnerRegular.of_le` proves that a measure below a finite inner regular
  measure is inner regular.
- `MeasureTheory.Measure.Regular.of_innerRegular` proves that a finite inner regular measure is
  regular.
- `MeasureTheory.Measure.Regular.map_of_continuous` proves that regularity passes along continuous
  maps.
- `MeasureTheory.Measure.InnerRegular.comap_subtype` proves that inner regularity passes to
  measurable subsets.

## iii. Table of contents

- A. Measures below inner regular measures
- B. Regularity from inner regularity

## iv. References

* None.

-/

@[expose] public section

open Set
open scoped ENNReal

namespace MeasureTheory.Measure

variable {α : Type*} [MeasurableSpace α] [TopologicalSpace α] {μ ν : Measure α}

/-!

## A. Measures below inner regular measures

-/

/-- A measure below a finite inner regular measure is inner regular. -/
lemma InnerRegular.of_le [OpensMeasurableSpace α] [T2Space α] [IsFiniteMeasure μ]
    [InnerRegular μ] (h : ν ≤ μ) : InnerRegular ν where
  innerRegular A hA r hr := by
    obtain ⟨K, hKA, hK, hAK⟩ :=
      hA.exists_isCompact_sdiff_lt (μ := μ) (measure_ne_top μ A) (tsub_pos_of_lt hr).ne'
    refine ⟨K, hKA, hK, lt_of_add_lt_add_right
      ((lt_tsub_iff_left.1 ((Measure.le_iff'.1 h _).trans_lt hAK)).trans_le
      ((measure_mono (union_sdiff_cancel hKA).ge).trans (measure_union_le _ _)))⟩

/-!

## B. Regularity from inner regularity

-/

/-- A finite inner regular measure on a Hausdorff space is regular. -/
lemma Regular.of_innerRegular [T2Space α] [BorelSpace α] [IsFiniteMeasure μ] [InnerRegular μ] :
    Regular μ :=
  { toOuterRegular := inferInstance
    lt_top_of_isCompact := fun _ _ => measure_lt_top _ _
    innerRegular := fun _ hU r hr => InnerRegular.innerRegular hU.measurableSet r hr }

/-- A measure below a finite inner regular measure on a Hausdorff space is regular. -/
lemma Regular.of_le [T2Space α] [BorelSpace α] [IsFiniteMeasure μ] [InnerRegular μ] (h : ν ≤ μ) :
    Regular ν :=
  have := InnerRegular.of_le h
  have := isFiniteMeasure_of_le μ h
  Regular.of_innerRegular

/-- A finite regular measure pushes forward to a regular measure along a continuous map into a
Hausdorff space. -/
lemma Regular.map_of_continuous {β : Type*} [TopologicalSpace β] [MeasurableSpace β]
    [BorelSpace β] [T2Space β] [BorelSpace α] [IsFiniteMeasure μ] [Regular μ] {f : α → β}
    (hf : Continuous f) : Regular (μ.map f) :=
  have : InnerRegular (μ.map f) := InnerRegular.map_of_continuous hf
  Regular.of_innerRegular

/-- An inner regular measure stays inner regular on a measurable subset. -/
lemma InnerRegular.comap_subtype [InnerRegular μ] {s : Set α} (hs : MeasurableSet s) :
    InnerRegular (μ.comap ((↑) : s → α)) :=
  ⟨InnerRegular.innerRegular.comap (MeasurableEmbedding.subtype_coe hs)
    (fun _ hU => (MeasurableEmbedding.subtype_coe hs).measurableSet_image' hU)
    (fun _ hK hKc => Topology.IsInducing.subtypeVal.isCompact_preimage' hKc hK)⟩

end MeasureTheory.Measure
