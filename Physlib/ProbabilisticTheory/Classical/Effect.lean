/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.ProbabilisticTheory.Classical.Basic
public import Mathlib.Order.Filter.IndicatorFunction

/-!
# Effects of classical theories

The indicator of an event is the yes-no test that passes exactly when the event occurs.

## i. Overview

An effect is a yes-no test. In a classical theory it is an observable with values between `0` and
`1`, the probability that the test passes in each configuration.

The indicator of an event passes exactly when the event occurs. Its expectation value in a state
is the probability of the event. Indicators of disjoint events add up to the indicator of their
union.

## ii. Key results

- `ProbabilisticTheory.Classical.indicator` : the indicator effect of an event.
- `ProbabilisticTheory.Classical.isLUB_sum_indicator` : the partial sums of the indicators of
  disjoint events increase to the indicator of their union.

## iii. Table of contents

- A. Indicators of events

## iv. References

-/

@[expose] public section

open Set

namespace ProbabilisticTheory.Classical

variable {X : Type*} [MeasurableSpace X]

/-! ## A. Indicators of events -/

/-- The indicator effect of an event `s`, with value `1` in `s` and `0` outside. -/
noncomputable def indicator (s : Event X) : Effect (measurable X) :=
  have h x : (s : Set X).indicator (1 : X → ℝ) x ∈ Icc 0 1 := by
    by_cases hx : x ∈ (s : Set X) <;> simp [hx]
  ⟨ofFun _ (measurable_one.indicator s.2) ⟨1, fun x ↦ abs_le.mpr ⟨by linarith [(h x).1], (h x).2⟩⟩,
    mem_effect_iff.mpr h⟩

@[simp] lemma coe_indicator (s : Event X) :
    ⇑(indicator s : Observables (measurable X)) = (s : Set X).indicator 1 := rfl

/-- The impossible event has the impossible effect. -/
@[simp] lemma indicator_empty : indicator (∅ : Event X) = 0 :=
  Subtype.ext (DFunLike.ext _ _ fun x ↦ by simp)

/-- The certain event has the certain effect. -/
@[simp] lemma indicator_top : indicator (⊤ : Event X) = 1 :=
  Subtype.ext (DFunLike.ext _ _ fun x ↦ by simp)

/-- In each configuration the indicators of disjoint events sum to the indicator of their union. -/
lemma hasSum_indicator {s : ℕ → Event X} (hd : Pairwise (Function.onFun Disjoint fun n ↦ (s n).1))
    (x : X) :
    HasSum (fun n ↦ (indicator (s n) : Observables (measurable X)) x)
      ((indicator ⟨⋃ n, (s n).1, .iUnion fun n ↦ (s n).2⟩ : Observables (measurable X)) x) := by
  simpa only [coe_indicator, HasSum, SummationFilter.unconditional_filter,
    ← Finset.indicator_biUnion_apply _ _ (hd.set_pairwise _)] using
    (tendsto_indicator_biUnion_finset _ 1 x).mono_right (pure_le_nhds _)

/-- The partial sums of the indicators of disjoint events increase to the indicator of their
union. -/
lemma isLUB_sum_indicator {s : ℕ → Event X}
    (hd : Pairwise (Function.onFun Disjoint fun n ↦ (s n).1)) :
    IsLUB (range fun N ↦ ∑ n ∈ Finset.range N, (indicator (s n) : Observables (measurable X)))
      (indicator ⟨⋃ n, (s n).1, .iUnion fun n ↦ (s n).2⟩ : Observables (measurable X)) :=
  isLUB_range_of_apply fun x ↦ by
    simpa only [sum_apply, Function.comp_def] using isLUB_of_tendsto_atTop
      ((Finset.sum_mono_set_of_nonneg fun n ↦ (mem_effect_iff.mp (indicator (s n)).2 x).1).comp
        Finset.range_mono) (hasSum_indicator hd x).tendsto_sum_nat

end ProbabilisticTheory.Classical
