/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.PontryaginDual
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Evaluation of Pontryagin characters

Evaluation at a fixed monoid element is continuous on the Pontryagin dual.

## i. Overview

Evaluation at a fixed monoid element is continuous on the Pontryagin dual. Its complex-valued
form is integrable against every finite measure. These lemmas supply the integrands for
Fourier–Stieltjes transforms, and apply to arbitrary monoids with a topology.

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

namespace TauCeti.PontryaginDual

variable {G : Type*} [Monoid G] [TopologicalSpace G]

/-- Complex-valued evaluation of a Pontryagin character at a fixed monoid element is continuous. -/
@[fun_prop]
lemma continuous_coe_eval_const (g : G) :
    Continuous (fun χ : _root_.PontryaginDual G => (χ g : ℂ)) :=
  continuous_subtype_val.comp (continuous_eval_const (F := G →ₜ* Circle) g)

variable [MeasurableSpace (_root_.PontryaginDual G)]
  [OpensMeasurableSpace (_root_.PontryaginDual G)]

/-- Complex-valued evaluation of a Pontryagin character is integrable against a finite measure. -/
lemma integrable_coe_eval
    {μ : Measure (_root_.PontryaginDual G)} [IsFiniteMeasure μ] (g : G) :
    Integrable (fun χ : _root_.PontryaginDual G => (χ g : ℂ)) μ :=
  (integrable_const (1 : ℝ)).mono'
    (continuous_coe_eval_const g).aestronglyMeasurable
    (.of_forall fun χ => by simp)

end TauCeti.PontryaginDual
