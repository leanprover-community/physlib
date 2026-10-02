/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.Classical.Channel
public import PhyslibAlpha.ProbabilisticTheory.Measurement.Pushforward

/-!
# Measurements

## i. Overview

A measurement with outcomes in `Ω` turns the system into a classical record: its outcome. So a
measurement is a channel from the system into the classical system of outcomes. In the Heisenberg
picture used here, it sends each observable `f` of the outcome, a bounded measurable function on
`Ω`, to the observable of the system whose expectation is the expectation of `f` after the
measurement. It is normal: it respects limits of increasing sequences.

The indicator of an event goes to the effect testing whether the outcome lands in it; these effects
form an effect-valued measure. In a normal state `ω` of the system, the outcome record is in the
normal state `ω ∘ M` of the classical system, which is a probability distribution over the outcomes:
the Born law. Measuring the outcome of a classical system itself is the identity channel.

## ii. Key results

- `Measurement Ω E` : a measurement with outcomes in `Ω`, a normal channel from the classical system
  of outcomes.
- `Measurement.toEffectValuedMeasure` : the effects of the events of a measurement.
- `Measurement.probabilityLaw` : the Born law of a measurement in a normal state.
- `Measurement.integral_probabilityLaw` : the average of `f` under the Born law is the expectation
  of `M f`.
- `Measurement.map` : measuring after a normal channel.
- `BoundedMeasurable.outcome` : measuring the outcome of a classical system.

## iii. Table of contents

- A. Measurements
- B. The Born law
- C. Measuring after a channel

-/

@[expose] public section

namespace ProbabilisticTheory

open MeasureTheory UnitalPositiveLinearMap

/-! ## A. Measurements -/

/-- A measurement with outcomes in `Ω`: a normal channel from the classical system of outcomes
into the system. -/
structure Measurement (Ω : Type*) [MeasurableSpace Ω] (E : Type*) [OrderUnitSpace E] where
  /-- The channel sending observables of the outcome to observables of the system. -/
  toChannel : Channel (BoundedMeasurable Ω) E
  /-- The channel is normal. -/
  isNormal : toChannel.IsNormal

namespace Measurement

variable {Ω E F : Type*} [MeasurableSpace Ω] [OrderUnitSpace E] [OrderUnitSpace F]

@[ext]
lemma ext {M N : Measurement Ω E} (h : M.toChannel = N.toChannel) : M = N := by
  cases M; cases N; congr

/-- The effect testing whether the outcome lies in an event. -/
noncomputable instance :
    CoeFun (Measurement Ω E) fun _ => ∀ s : Set Ω, MeasurableSet s → Effect E where
  coe M s hs := M.toChannel.mapEffect (BoundedMeasurable.indicatorEffect s hs)

lemma coe_apply (M : Measurement Ω E) (s : Set Ω) (hs : MeasurableSet s) :
    (M s hs : E) = M.toChannel (BoundedMeasurable.indicator s hs) := rfl

/-- The effects of the events of a measurement form an effect-valued measure. -/
noncomputable def toEffectValuedMeasure (M : Measurement Ω E) : EffectValuedMeasure Ω E :=
  BoundedMeasurable.outcomeMeasurement.map M.toChannel M.isNormal

@[simp]
lemma toEffectValuedMeasure_apply (M : Measurement Ω E) (s : Set Ω) (hs : MeasurableSet s) :
    M.toEffectValuedMeasure s hs = M s hs := rfl

@[simp]
lemma map_empty (M : Measurement Ω E) : M ∅ .empty = 0 := M.toEffectValuedMeasure.map_empty

@[simp]
lemma map_univ (M : Measurement Ω E) : M .univ .univ = 1 := M.toEffectValuedMeasure.map_univ

/-! ## B. The Born law -/

lemma isNormal_comp (M : Measurement Ω E) {ω : 𝓢[ℝ, E]} (hω : ω.IsNormal) :
    (ω.comp M.toChannel).IsNormal :=
  UnitalPositiveLinearMap.IsNormal.comp M.isNormal hω

/-- The Born law: the distribution of the outcome of `M` in the normal state `ω`. -/
noncomputable def probabilityLaw (M : Measurement Ω E) (ω : 𝓢[ℝ, E]) (hω : ω.IsNormal) :
    ProbabilityMeasure Ω :=
  BoundedMeasurable.toMeasure (ω.comp M.toChannel) (M.isNormal_comp hω)

@[simp]
lemma probabilityLaw_apply (M : Measurement Ω E) (ω : 𝓢[ℝ, E]) (hω : ω.IsNormal)
    (s : Set Ω) (hs : MeasurableSet s) :
    (M.probabilityLaw ω hω : Measure Ω) s = ENNReal.ofReal (ω (M s hs)) :=
  BoundedMeasurable.toMeasure_apply _ _ hs

/-- The average of an observable `f` of the outcome under the Born law is the expectation of
`M f`. -/
lemma integral_probabilityLaw (M : Measurement Ω E) (ω : 𝓢[ℝ, E]) (hω : ω.IsNormal)
    (f : BoundedMeasurable Ω) : ∫ x, f x ∂(M.probabilityLaw ω hω : Measure Ω) = ω (M.toChannel f) :=
  congrFun (congrArg DFunLike.coe (BoundedMeasurable.ofMeasure_toMeasure _ (M.isNormal_comp hω))) f

/-- The Born law of a measurement is the Born law of its effect-valued measure. -/
lemma probabilityLaw_eq (M : Measurement Ω E) (ω : 𝓢[ℝ, E]) (hω : ω.IsNormal) :
    M.probabilityLaw ω hω = M.toEffectValuedMeasure.probabilityLaw ω hω :=
  ProbabilityMeasure.toMeasure_injective <| Measure.ext fun s hs => by
    rw [probabilityLaw_apply _ _ _ s hs, EffectValuedMeasure.probabilityLaw_apply _ _ _ s hs,
      toEffectValuedMeasure_apply]

/-! ## C. Measuring after a channel -/

/-- Measuring `M` after the normal channel `φ`: the outcome observables go through `M`, then
through `φ`. -/
def map (M : Measurement Ω E) (φ : Channel E F) (hφ : φ.IsNormal) : Measurement Ω F where
  toChannel := φ.comp M.toChannel
  isNormal := UnitalPositiveLinearMap.IsNormal.comp M.isNormal hφ

@[simp, nolint simpNF]
lemma coe_map_apply (M : Measurement Ω E) (φ : Channel E F) (hφ : φ.IsNormal) (s : Set Ω)
    (hs : MeasurableSet s) : (M.map φ hφ s hs : F) = φ (M s hs) := rfl

end Measurement

end ProbabilisticTheory

namespace BoundedMeasurable
open ProbabilisticTheory
open MeasureTheory UnitalPositiveLinearMap
open MeasureTheory UnitalPositiveLinearMap

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Measuring the outcome of a classical system. -/
def outcome : Measurement Ω (BoundedMeasurable Ω) where
  toChannel := .id ℝ _
  isNormal := isNormal_id

@[simp, nolint simpNF]
lemma coe_outcome_apply (s : Set Ω) (hs : MeasurableSet s) :
    (outcome s hs : BoundedMeasurable Ω) = BoundedMeasurable.indicator s hs := rfl

/-- The outcome of a classical system in a normal state is distributed by the state. -/
lemma probabilityLaw_outcome (ω : 𝓢[ℝ, BoundedMeasurable Ω]) (hω : ω.IsNormal) :
    outcome.probabilityLaw ω hω = toMeasure ω hω := by
  simp only [Measurement.probabilityLaw, outcome, comp_id]

end BoundedMeasurable

