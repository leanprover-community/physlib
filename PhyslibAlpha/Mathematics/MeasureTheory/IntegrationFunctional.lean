/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.Topology.ContinuousMap.Compact

/-!
# Integration as a continuous functional

Integration against a finite measure as a continuous linear functional on `C(X, ℝ)`.

## i. Overview

On a compact space, integrating continuous functions against a finite measure is linear and
continuous in the supremum norm.

## ii. Key results

- `MeasureTheory.integralCLM` is integration against a finite measure on `C(X, ℝ)`.

## iii. Table of contents

- A. Integration as a continuous functional

## iv. References

* None.

-/

@[expose] public section

/-!

## A. Integration as a continuous functional

-/

namespace MeasureTheory

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X]

lemma integrable_continuousMap (μ : Measure X) [IsFiniteMeasure μ] (g : C(X, ℝ)) :
    Integrable g μ :=
  .of_bound g.continuous.aestronglyMeasurable ‖g‖ (.of_forall g.norm_coe_le_norm)

/-- Integration of continuous functions against a finite measure, as a continuous functional. -/
noncomputable def integralCLM (μ : Measure X) [IsFiniteMeasure μ] : C(X, ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous ⟨⟨fun g => ∫ x, g x ∂μ, fun g h =>
    integral_add (integrable_continuousMap μ g) (integrable_continuousMap μ h)⟩,
    fun c _ => integral_const_mul c _⟩ (μ.real Set.univ) fun g => by
      simpa [mul_comm] using
        norm_integral_le_of_norm_le_const (μ := μ) (.of_forall g.norm_coe_le_norm)

@[simp] lemma integralCLM_apply (μ : Measure X) [IsFiniteMeasure μ] (g : C(X, ℝ)) :
    integralCLM μ g = ∫ x, g x ∂μ := rfl

end MeasureTheory
