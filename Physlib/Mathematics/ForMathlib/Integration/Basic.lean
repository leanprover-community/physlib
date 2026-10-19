/-
Copyright (c) 2026 Art Mountain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Art Mountain
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
/-!
# Basic integration results

Basic results related to integration not in Mathlib.

## i. Overview

Mathlib's `MeasureTheory.integral_withDensity_eq_integral_smul` converts an integral against a
measure `μ.withDensity f` into an integral against `μ`, but it takes the density as an
`NNReal`-valued function.

This file contains the version of that lemma for densities given as real-valued functions.

## ii. Key results

- `Integration.integral_withDensity_ofReal_eq_integral_smul` : for measurable `f ≥ 0`,
  `∫ x, g x ∂(μ.withDensity fun x => ENNReal.ofReal (f x)) = ∫ x, f x • g x ∂μ`.

## iii. Table of contents

- A. Integrals against a real-valued density

## iv. References

-/

@[expose] public section

namespace Integration

/-! ## A. Integrals against a real-valued density -/

open MeasureTheory in
/-- Integrating `g` against the measure with real-valued density `f` (taken through
`ENNReal.ofReal`) is integrating `f x • g x` against the original measure, for measurable
`f` that is everywhere nonnegative. This is the `ℝ`-valued form of
`integral_withDensity_eq_integral_smul`, which takes an `NNReal`-valued density. -/
lemma integral_withDensity_ofReal_eq_integral_smul {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : α → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (g : α → E) :
    ∫ x, g x ∂(μ.withDensity fun x => ENNReal.ofReal (f x)) = ∫ x, f x • g x ∂μ := by
  refine (integral_withDensity_eq_integral_smul
    (f := fun x => Real.toNNReal (f x)) hf.real_toNNReal g).trans ?_
  congr 1
  funext x
  rw [NNReal.smul_def, Real.coe_toNNReal _ (hf0 x)]

end Integration
