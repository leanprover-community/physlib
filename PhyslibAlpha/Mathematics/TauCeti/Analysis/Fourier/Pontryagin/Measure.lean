/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import PhyslibAlpha.Mathematics.TauCeti.Analysis.Fourier.Pontryagin.DualEval
public import Mathlib.MeasureTheory.Measure.FiniteMeasure

/-!
# Fourier–Stieltjes transform of measures on a Pontryagin dual

Integrating character evaluations against a finite positive measure on the Pontryagin dual defines a
complex-valued function on the original additive group.

## i. Overview

Integrating character evaluations against a finite positive measure on the Pontryagin dual
defines a complex-valued function on the original additive group. The transform records the
measure's mass at the identity and respects addition, scaling, and point masses.

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

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G]
  [MeasurableSpace (PontryaginDual (Multiplicative G))]

/-- The Fourier–Stieltjes transform of a finite measure on the Pontryagin dual of an
additive group. -/
noncomputable def _root_.MeasureTheory.FiniteMeasure.pontryaginMeasureTransform
    (μ : FiniteMeasure (PontryaginDual (Multiplicative G))) (g : G) : ℂ :=
  ∫ χ, (χ (Multiplicative.ofAdd g) : ℂ) ∂μ.toMeasure

/-- The transform evaluated at a group element is the integral of character evaluations. -/
lemma _root_.MeasureTheory.FiniteMeasure.pontryaginMeasureTransform_apply
    (μ : FiniteMeasure (PontryaginDual (Multiplicative G))) (g : G) :
    μ.pontryaginMeasureTransform g =
      ∫ χ, (χ (Multiplicative.ofAdd g) : ℂ) ∂μ.toMeasure := by
  unfold FiniteMeasure.pontryaginMeasureTransform
  rfl

/-- At the identity, the transform records the total mass of the measure. -/
@[simp]
lemma _root_.MeasureTheory.FiniteMeasure.pontryaginMeasureTransform_zero
    (μ : FiniteMeasure (PontryaginDual (Multiplicative G))) :
    μ.pontryaginMeasureTransform 0 = (μ.toMeasure.real Set.univ : ℂ) := by
  simp [FiniteMeasure.pontryaginMeasureTransform]

/-- The transform of the zero measure vanishes. -/
@[simp]
lemma _root_.MeasureTheory.FiniteMeasure.pontryaginMeasureTransform_zero_measure :
    (0 : FiniteMeasure (PontryaginDual (Multiplicative G))).pontryaginMeasureTransform = 0 := by
  funext g
  simp [FiniteMeasure.pontryaginMeasureTransform]

/-- The transform commutes with nonnegative scalar multiplication of finite measures. -/
@[simp]
lemma _root_.MeasureTheory.FiniteMeasure.pontryaginMeasureTransform_smul
    (c : NNReal) (μ : FiniteMeasure (PontryaginDual (Multiplicative G))) :
    (c • μ).pontryaginMeasureTransform = c • μ.pontryaginMeasureTransform := by
  funext g
  simp [FiniteMeasure.pontryaginMeasureTransform]

variable [OpensMeasurableSpace (PontryaginDual (Multiplicative G))]

/-- The transform commutes with addition of finite measures. -/
@[simp]
lemma _root_.MeasureTheory.FiniteMeasure.pontryaginMeasureTransform_add
    (μ ν : FiniteMeasure (PontryaginDual (Multiplicative G))) :
    (μ + ν).pontryaginMeasureTransform =
      μ.pontryaginMeasureTransform + ν.pontryaginMeasureTransform := by
  funext g
  unfold FiniteMeasure.pontryaginMeasureTransform
  rw [FiniteMeasure.toMeasure_add,
    integral_add_measure
      (PontryaginDual.integrable_coe_eval (μ := μ.toMeasure) (Multiplicative.ofAdd g))
      (PontryaginDual.integrable_coe_eval (μ := ν.toMeasure) (Multiplicative.ofAdd g))]
  rfl

/-- The transform of a point mass is its character. -/
@[simp]
lemma _root_.MeasureTheory.FiniteMeasure.pontryaginMeasureTransform_dirac
    (χ : PontryaginDual (Multiplicative G)) (g : G) :
    FiniteMeasure.pontryaginMeasureTransform
      (⟨Measure.dirac χ, inferInstance⟩ : FiniteMeasure
        (PontryaginDual (Multiplicative G))) g =
      (χ (Multiplicative.ofAdd g) : ℂ) := by
  simp [FiniteMeasure.pontryaginMeasureTransform,
    integral_dirac' _ _
      (PontryaginDual.continuous_coe_eval_const (Multiplicative.ofAdd g)).stronglyMeasurable]

end TauCeti
