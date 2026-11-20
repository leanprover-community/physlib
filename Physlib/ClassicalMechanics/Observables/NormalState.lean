/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.ClassicalMechanics.Observables.Measurable
public import Physlib.ProbabilisticTheory.OrderUnit.Cone
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Normal classical states

The normal states of a classical system are the probability distributions of its configuration.

## i. Overview

A probability distribution `μ` of configurations gives a state. It assigns each observable its
average `∫ f dμ`, and monotone convergence makes this state normal. A distribution concentrated
at one configuration gives the Dirac state there.

A normal state is determined by the probabilities it assigns to events. Every positive
observable is the supremum of an increasing sequence of simple observables, which are finite
combinations of event indicators. Normality carries the agreement on events up to these
suprema.

Conversely a normal state assigns each event `s` the probability `ω (indicator s)`. Normality
makes these probabilities countably additive, so they form a probability distribution of
configurations. The two constructions are inverse. Every normal state is therefore the mixture
`f ↦ ∫ f(x) dμ(x)` of Dirac states with exactly one probability distribution `μ`. This
uniqueness of the decomposition into pure states is the defining feature of classical
statistics. A mixed quantum state has many decompositions into pure states.

## ii. Key results

- `ProbabilisticTheory.Classical.ofMeasure` : the state of a probability distribution.
- `ProbabilisticTheory.Classical.ext_of_isNormal` : normal states are determined by the
  probabilities of events.
- `ProbabilisticTheory.Classical.toMeasure` : the probability distribution of a normal state.
- `ProbabilisticTheory.Classical.normalStateEquiv` : normal states are probability
  distributions.

## iii. Table of contents

- A. States of probability distributions
- B. Normal states are determined by events
- C. Probability distributions of normal states
- D. Normal states are probability distributions

## iv. References

-/

@[expose] public section

namespace ProbabilisticTheory.Classical

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## A. States of probability distributions -/

/-- The state of a probability distribution assigns each observable its average. -/
noncomputable def ofMeasure (μ : ProbabilityMeasure Ω) : ClassicalState Ω :=
  .ofLinearMap
    { toFun f := ∫ x, toFun f x ∂(μ : Measure Ω)
      map_add' f g := by
        rw [map_add]
        exact integral_add (integrable_toFun f _) (integrable_toFun g _)
      map_smul' c f := by rw [map_smul]; exact integral_smul c _ }
    (fun f hf ↦ integral_nonneg (toFun_le_toFun_iff.mpr hf)) (by simp)

@[simp]
lemma ofMeasure_apply (μ : ProbabilityMeasure Ω) (f : ClassicalObservable Ω) :
    ofMeasure μ f = ∫ x, toFun f x ∂(μ : Measure Ω) := rfl

/-- The average of an event indicator is the probability of the event. -/
lemma ofMeasure_indicator (μ : ProbabilityMeasure Ω) {s : Set Ω} (hs : MeasurableSet s) :
    ofMeasure μ (indicator s hs) = (μ : Measure Ω).real s := by
  rw [ofMeasure_apply, toFun_indicator, integral_indicator_one hs]

/-- A distribution concentrated at one configuration gives the Dirac state there. -/
lemma ofMeasure_dirac (x : Ω) :
    ofMeasure ⟨Measure.dirac x, inferInstance⟩ = dirac x :=
  Channel.ext fun f ↦ integral_dirac' _ x (measurable_toFun f).stronglyMeasurable

/-- The state of a probability distribution is normal by monotone convergence. -/
lemma isNormal_ofMeasure (μ : ProbabilityMeasure Ω) : (ofMeasure μ).IsNormal := fun f g hf hg ↦
  have hmono x : Monotone fun n ↦ toFun (f n) x := fun _ _ h ↦ toFun_le_toFun_iff.mpr (hf h) x
  isLUB_of_tendsto_atTop
    (fun _ _ h ↦ integral_mono (integrable_toFun _ _) (integrable_toFun _ _)
      (toFun_le_toFun_iff.mpr (hf h)))
    (integral_tendsto_of_tendsto_of_monotone (fun n ↦ integrable_toFun (f n) _)
      (integrable_toFun g _) (.of_forall hmono)
      (.of_forall fun x ↦ tendsto_atTop_isLUB (hmono x) (isLUB_range_iff.mp hg x)))

/-! ## B. Normal states are determined by events -/

/-- States that assign the same probabilities to all events agree on simple observables. -/
lemma apply_ofSimpleFunc_eq {φ ψ : ClassicalState Ω}
    (h : ∀ s hs, φ (indicator s hs) = ψ (indicator s hs)) (f : SimpleFunc Ω ℝ) :
    φ (ofSimpleFunc f) = ψ (ofSimpleFunc f) :=
  LinearMap.eqOn_span' (f := φ.toLinearMap) (g := ψ.toLinearMap)
    (by rintro _ ⟨s, hs, rfl⟩; exact h s hs) (ofSimpleFunc_mem_span f)

/-- Normal states that assign the same probabilities to all events are equal. -/
lemma ext_of_isNormal {φ ψ : ClassicalState Ω} (hφ : φ.IsNormal) (hψ : ψ.IsNormal)
    (h : ∀ s hs, φ (indicator s hs) = ψ (indicator s hs)) : φ = ψ := by
  have hpos (f : ClassicalObservable Ω) (hf : 0 ≤ f) : φ f = ψ f :=
    (hφ _ _ (monotone_approx f) (isLUB_approx hf)).unique <| by
      simpa only [Function.comp_def, approx, apply_ofSimpleFunc_eq h] using
        hψ _ _ (monotone_approx f) (isLUB_approx hf)
  refine Channel.ext fun f ↦ ?_
  obtain ⟨p, q, rfl⟩ := PosCone.exists_sub f
  rw [map_sub, map_sub, hpos p p.2, hpos q q.2]

/-! ## C. Probability distributions of normal states -/

variable (ω : ClassicalState Ω) (hω : ω.IsNormal)

include hω in
/-- A normal state assigns countably additive probabilities to disjoint events. -/
lemma ofReal_apply_indicator_iUnion {s : ℕ → Set Ω} (hs : ∀ n, MeasurableSet (s n))
    (hd : Pairwise (Function.onFun Disjoint s)) :
    ENNReal.ofReal (ω (indicator (⋃ n, s n) (.iUnion hs))) =
      ∑' n, ENNReal.ofReal (ω (indicator (s n) (hs n))) := by
  have hm := (Finset.sum_mono_set_of_nonneg fun n ↦ indicator_nonneg (s n) (hs n)).comp
    Finset.range_mono
  refine tendsto_nhds_unique ?_ ENNReal.summable.hasSum.tendsto_sum_nat
  simpa only [Function.comp_def, map_sum, ENNReal.ofReal_sum_of_nonneg
    fun n _ ↦ map_nonneg ω (indicator_nonneg (s n) (hs n))] using ENNReal.tendsto_ofReal
      (tendsto_atTop_isLUB ((OrderHomClass.mono ω).comp hm) (hω _ _ hm (isLUB_sum_indicator hs hd)))

/-- The probability distribution of a normal state gives each event its probability in the
state. -/
noncomputable def toMeasure : ProbabilityMeasure Ω :=
  ⟨Measure.ofMeasurable (fun s hs ↦ ENNReal.ofReal (ω (indicator s hs)))
    (by rw [indicator_empty, map_zero, ENNReal.ofReal_zero])
    (fun _ hs hd ↦ ofReal_apply_indicator_iUnion ω hω hs hd),
    ⟨by rw [Measure.ofMeasurable_apply _ .univ, indicator_univ, map_one, ENNReal.ofReal_one]⟩⟩

lemma toMeasure_apply {s : Set Ω} (hs : MeasurableSet s) :
    (toMeasure ω hω : Measure Ω) s = ENNReal.ofReal (ω (indicator s hs)) :=
  Measure.ofMeasurable_apply (mU := fun _ hs hd ↦ ofReal_apply_indicator_iUnion ω hω hs hd) s hs

lemma measureReal_toMeasure {s : Set Ω} (hs : MeasurableSet s) :
    (toMeasure ω hω : Measure Ω).real s = ω (indicator s hs) := by
  rw [measureReal_def, toMeasure_apply ω hω hs,
    ENNReal.toReal_ofReal (map_nonneg ω (indicator_nonneg s hs))]

/-! ## D. Normal states are probability distributions -/

/-- The normal states of a classical system are the probability distributions of its
configuration. Every normal state is the mixture `f ↦ ∫ f(x) dμ(x)` of Dirac states with
exactly one probability distribution `μ`. -/
noncomputable def normalStateEquiv : {ω : ClassicalState Ω // ω.IsNormal} ≃ ProbabilityMeasure Ω
    where
  toFun ω := toMeasure ω.1 ω.2
  invFun μ := ⟨ofMeasure μ, isNormal_ofMeasure μ⟩
  left_inv ω := Subtype.ext <| ext_of_isNormal (isNormal_ofMeasure _) ω.2 fun s hs ↦ by
    rw [ofMeasure_indicator _ hs, measureReal_toMeasure _ _ hs]
  right_inv μ := ProbabilityMeasure.toMeasure_injective <| Measure.ext fun s hs ↦ by
    rw [toMeasure_apply _ _ hs, ofMeasure_indicator _ hs, ofReal_measureReal]

end ProbabilisticTheory.Classical
