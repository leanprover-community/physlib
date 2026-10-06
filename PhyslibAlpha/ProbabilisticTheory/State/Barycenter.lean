/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.State.StateSpace
public import Mathlib.MeasureTheory.Measure.DiracProba
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Barycenters of random states

The barycenter of a probability measure on states: the state a random preparation produces.

## i. Overview

A probability measure `μ` on the states is a random state: pick a state `ω` according to `μ`, then
measure. The expectation value of an observable `A` is then the average of `ω A`. These averages
form a state again, the barycenter of `μ`. It is the state that the random procedure prepares.

## ii. Key results

- `UnitalPositiveLinearMap.barycenter` is the barycenter of a probability measure on states.

## iii. Table of contents

- A. Integrability of expectation values
- B. Barycenters

## iv. References

* None.

-/

@[expose] public section

namespace ProbabilisticTheory

open StateSpace

open MeasureTheory ArchimedeanOrderUnitSpace Filter Topology

variable {E : Type*} [ArchimedeanOrderUnitSpace E]

namespace UnitalPositiveLinearMap

/-!

## A. Integrability of expectation values

-/

/-- An expectation value is integrable against every probability measure on states. -/
lemma integrable_apply (μ : ProbabilityMeasure (stateSpace E)) (A : E) :
    Integrable (fun ω : stateSpace E => toState ω A) (μ : Measure (stateSpace E)) :=
  Integrable.of_bound (StateSpace.continuous_apply A).aestronglyMeasurable (orderUnitNorm A)
    (.of_forall fun ω => abs_apply_le_orderUnitNorm (toState ω) A)

/-!

## B. Barycenters

-/

/-- The barycenter of `μ`: the state predicting, for every observable, the `μ`-average of the
predictions. -/
noncomputable def barycenter (μ : ProbabilityMeasure (stateSpace E)) : 𝓢[ℝ, E] :=
  ofLinearMap
    { toFun A := ∫ ω : stateSpace E, toState ω A ∂(μ : Measure (stateSpace E))
      map_add' A B := by
        simp only [map_add]
        exact integral_add (integrable_apply μ A) (integrable_apply μ B)
      map_smul' r A := by
        simp only [map_smul, smul_eq_mul, RingHom.id_apply]
        exact integral_const_mul r _ }
    (fun _ hA => integral_nonneg fun ω => map_nonneg (toState ω) hA)
    (by simp)

@[simp]
lemma barycenter_apply (μ : ProbabilityMeasure (stateSpace E)) (A : E) :
    barycenter μ A = ∫ ω : stateSpace E, toState ω A ∂(μ : Measure (stateSpace E)) := rfl

end UnitalPositiveLinearMap

end ProbabilisticTheory
