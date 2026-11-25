/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.ProbabilisticTheory.Classical.Dirac
public import Physlib.Mathematics.ForMathlib.SimpleFunc
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Normal classical states

The normal states of a classical system are the probability distributions of its configuration.

## i. Overview

A probability distribution `μ` of configurations gives a state. It assigns each observable its
average `∫ f dμ`. Monotone convergence makes this state normal. A distribution concentrated
at one configuration gives the Dirac state there.

A normal state is determined by the probabilities it assigns to events. Every positive
observable is the supremum of an increasing sequence of observables with finitely many values,
which are finite combinations of indicators. Normality carries the agreement on events up
to these suprema.

Conversely a normal state assigns each event `s` the probability `ω (indicator s)`. Normality
makes these probabilities countably additive, so they form a probability distribution of
configurations. The two constructions are inverse. Every normal state is therefore the mixture
`f ↦ ∫ f(x) dμ(x)` of Dirac states with exactly one probability distribution `μ`. This
uniqueness of the decomposition into pure states is the defining feature of classical
statistics. A mixed quantum state has many decompositions into pure states.

## ii. Key results

- `ProbabilisticTheory.Classical.ofDistribution` : the state of a probability distribution.
- `ProbabilisticTheory.Classical.ext_of_isNormal` : normal states are determined by the
  probabilities of events.
- `ProbabilisticTheory.Classical.distribution` : the probability distribution of a normal
  state.
- `ProbabilisticTheory.Classical.distributionEquiv` : normal states are probability
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

variable {X : Type*} [MeasurableSpace X]

/-! ## A. States of probability distributions -/

/-- Every observable is integrable for a finite measure on configurations. -/
lemma integrable (f : Observables (measurable X)) (μ : Measure X) [IsFiniteMeasure μ] :
    Integrable f μ :=
  have ⟨_, hC⟩ := exists_abs_le f
  .of_bound (measurable_coe f).aestronglyMeasurable _ (.of_forall hC)

/-- The state of a probability distribution `μ` assigns each observable its average. -/
noncomputable def ofDistribution (μ : Measure X) [IsProbabilityMeasure μ] : State (measurable X) :=
  .ofLinearMap
    { toFun f := ∫ x, f x ∂μ
      map_add' f g := by simpa using integral_add (integrable f μ) (integrable g μ)
      map_smul' c f := by simpa using integral_const_mul c f }
    (fun f hf ↦ integral_nonneg (le_def.mp hf)) (by simp)

variable (μ : Measure X) [IsProbabilityMeasure μ]

@[simp]
lemma ofDistribution_apply (f : Observables (measurable X)) :
    ofDistribution μ f = ∫ x, f x ∂μ := rfl

/-- The average of the indicator of an event is the probability of the event. -/
lemma ofDistribution_indicator (s : Event X) :
    ofDistribution μ (indicator s) = μ.real s := by
  rw [ofDistribution_apply, coe_indicator, integral_indicator_one s.2]

/-- A distribution concentrated at one configuration gives the Dirac state there. -/
lemma ofDistribution_dirac (x : X) :
    ofDistribution (Measure.dirac x) = dirac _ x :=
  Channel.ext fun f ↦ integral_dirac' _ x (measurable_coe f).stronglyMeasurable

/-- The state of a probability distribution is normal by monotone convergence. -/
lemma isNormal_ofDistribution : (ofDistribution μ).IsNormal := fun f g hf hg ↦
  have hmono x : Monotone (f · x) := fun _ _ h ↦ le_def.mp (hf h) x
  isLUB_of_tendsto_atTop
    (fun _ _ h ↦ integral_mono (integrable _ _) (integrable _ _) (le_def.mp (hf h)))
    (integral_tendsto_of_tendsto_of_monotone (fun n ↦ integrable (f n) _)
      (integrable g _) (.of_forall hmono)
      (.of_forall fun x ↦ tendsto_atTop_isLUB (hmono x) (isLUB_range_apply hg x)))

/-! ## B. Normal states are determined by events -/

/-- The increasing approximation of an observable by observables with finitely many values. -/
noncomputable def approx (f : Observables (measurable X)) (n : ℕ) : Observables (measurable X) :=
  ofFun (SimpleFunc.realApprox f n) (SimpleFunc.realApprox f n).measurable
    ((SimpleFunc.realApprox f n).map abs).exists_forall_le

lemma monotone_approx (f : Observables (measurable X)) : Monotone (approx f) :=
  fun _ _ h ↦ le_def.mpr (SimpleFunc.monotone_realApprox f h)

/-- A positive observable is the supremum of its increasing approximations. -/
lemma isLUB_approx {f : Observables (measurable X)} (hf : 0 ≤ f) : IsLUB (Set.range (approx f)) f :=
  isLUB_range_of_apply fun x ↦ isLUB_of_tendsto_atTop
    (fun _ _ h ↦ le_def.mp (monotone_approx f h) x)
    (SimpleFunc.tendsto_realApprox (measurable_coe f) (by simpa using le_def.mp hf x))

/-- States with the same probabilities of events agree on the approximations of an observable,
which are finite combinations of indicators. -/
lemma apply_approx_eq {φ ψ : State (measurable X)}
    (h : ∀ s : Event X, φ (indicator s) = ψ (indicator s))
    (f : Observables (measurable X)) (n : ℕ) :
    φ (approx f n) = ψ (approx f n) := by
  set g := SimpleFunc.realApprox f n
  have hg : approx f n = ∑ y ∈ g.range,
      y • (indicator ⟨g ⁻¹' {y}, g.measurableSet_preimage _⟩ : Observables (measurable X)) :=
    DFunLike.ext _ _ fun x ↦ by
      simp only [sum_apply, smul_apply, coe_indicator]
      exact (g.sum_range_mul_indicator x).symm
  simp [hg, h]

/-- Normal states that assign the same probabilities to all events are equal. -/
lemma ext_of_isNormal {φ ψ : State (measurable X)} (hφ : φ.IsNormal) (hψ : ψ.IsNormal)
    (h : ∀ s : Event X, φ (indicator s) = ψ (indicator s)) : φ = ψ := by
  have hpos (f : Observables (measurable X)) (hf : 0 ≤ f) : φ f = ψ f :=
    (hφ _ _ (monotone_approx f) (isLUB_approx hf)).unique <| by
      simpa only [Function.comp_def, apply_approx_eq h] using
        hψ _ _ (monotone_approx f) (isLUB_approx hf)
  refine Channel.ext fun f ↦ ?_
  obtain ⟨p, q, rfl⟩ := PosCone.exists_sub f
  rw [map_sub, map_sub, hpos p p.2, hpos q q.2]

/-! ## C. Probability distributions of normal states -/

variable (ω : State (measurable X)) (hω : ω.IsNormal)

include hω in
/-- A normal state assigns countably additive probabilities to disjoint events. -/
lemma ofReal_apply_indicator_iUnion {s : ℕ → Event X}
    (hd : Pairwise (Function.onFun Disjoint fun n ↦ (s n).1)) :
    ENNReal.ofReal (ω (indicator ⟨⋃ n, (s n).1, .iUnion fun n ↦ (s n).2⟩)) =
      ∑' n, ENNReal.ofReal (ω (indicator (s n))) := by
  have hm := (Finset.sum_mono_set_of_nonneg fun n ↦ (indicator (s n)).2.1).comp
    Finset.range_mono
  refine tendsto_nhds_unique ?_ CompleteLattice.summable.hasSum.tendsto_sum_nat
  simpa only [Function.comp_def, map_sum, ENNReal.ofReal_sum_of_nonneg
    fun n _ ↦ map_nonneg ω ((indicator (s n)).2.1)] using ENNReal.tendsto_ofReal
      (tendsto_atTop_isLUB ((OrderHomClass.mono ω).comp hm) (hω _ _ hm (isLUB_sum_indicator hd)))

/-- The probability distribution of a normal state gives each event its probability in the
state. -/
noncomputable def distribution : Measure X :=
  Measure.ofMeasurable (fun s hs ↦ ENNReal.ofReal (ω (indicator ⟨s, hs⟩)))
    (show ENNReal.ofReal (ω (indicator (∅ : Event X))) = 0 by simp)
    (fun f hf hd ↦ ofReal_apply_indicator_iUnion ω hω (s := fun n ↦ ⟨f n, hf n⟩) hd)

lemma distribution_apply (s : Event X) :
    distribution ω hω s = ENNReal.ofReal (ω (indicator s)) :=
  Measure.ofMeasurable_apply _ s.2

instance : IsProbabilityMeasure (distribution ω hω) :=
  ⟨by simpa using distribution_apply ω hω ⊤⟩

/-- The probability of an event in the distribution of a normal state is its probability in the
state. -/
lemma measureReal_distribution (s : Event X) :
    (distribution ω hω).real s = ω (indicator s) := by
  rw [measureReal_def, distribution_apply ω hω s,
    ENNReal.toReal_ofReal (map_nonneg ω (indicator s).2.1)]

/-! ## D. Normal states are probability distributions -/

/-- A normal state is the average over its distribution. -/
lemma ofDistribution_distribution : ofDistribution (distribution ω hω) = ω :=
  ext_of_isNormal (isNormal_ofDistribution _) hω fun s ↦ by
    rw [ofDistribution_indicator, measureReal_distribution]

/-- The distribution of the state of a probability distribution is the distribution itself. -/
lemma distribution_ofDistribution :
    distribution (ofDistribution μ) (isNormal_ofDistribution μ) = μ :=
  Measure.ext fun s hs ↦ by
    rw [distribution_apply _ _ ⟨s, hs⟩, ofDistribution_indicator, ofReal_measureReal]

/-- The normal states of a classical system are the probability distributions of its
configuration. Every normal state is the mixture `f ↦ ∫ f(x) dμ(x)` of Dirac states with
exactly one probability distribution `μ`. -/
noncomputable def distributionEquiv :
    {ω : State (measurable X) // ω.IsNormal} ≃ ProbabilityMeasure X where
  toFun ω := ⟨distribution ω.1 ω.2, inferInstance⟩
  invFun μ := ⟨ofDistribution μ, isNormal_ofDistribution (μ : Measure X)⟩
  left_inv ω := Subtype.ext (ofDistribution_distribution ω.1 ω.2)
  right_inv μ := Subtype.ext (distribution_ofDistribution (μ : Measure X))

/-- Different probability distributions give different states. -/
lemma ofDistribution_injective {ν : Measure X} [IsProbabilityMeasure ν]
    (h : ofDistribution μ = ofDistribution ν) : μ = ν :=
  congrArg Subtype.val <| distributionEquiv.symm.injective
    (a₁ := ⟨μ, inferInstance⟩) (a₂ := ⟨ν, inferInstance⟩) (Subtype.ext h)

end ProbabilisticTheory.Classical
