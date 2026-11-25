/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.ProbabilisticTheory.Classical.Basic
public import Mathlib.MeasureTheory.Function.SpecialFunctions.RCLike

/-!
# The measurable classical theory

The observables of a classical system on a measurable space are its bounded measurable functions.

## i. Overview

On a measurable space `X` of configurations the observables are the bounded measurable real
functions. They form the classical theory `measurable X`. Its events are the measurable sets of
configurations.

Countably many observables bounded above have a pointwise supremum, which is again an
observable. Their least upper bound is exactly this pointwise supremum.

## ii. Key results

- `ProbabilisticTheory.Classical.measurable` : the classical theory of bounded measurable
  observables.
- `ProbabilisticTheory.Classical.Event` : the events, measurable sets of configurations.
- `ProbabilisticTheory.Classical.Event.iUnion` : the union of countably many events.
- `ProbabilisticTheory.Classical.ofFun` : a bounded measurable real function as an observable.
- `ProbabilisticTheory.Classical.isLUB_range_apply` : the least upper bound of countably many
  observables is their pointwise supremum.

## iii. Table of contents

- A. Observables of a measurable space
- B. Suprema of countable families

## iv. References

-/

@[expose] public section

open Set

namespace ProbabilisticTheory.Classical

/-! ## A. Observables of a measurable space -/

/-- The classical theory whose observables are the bounded measurable functions of the
configuration. -/
noncomputable abbrev measurable (X : Type*) [MeasurableSpace X] : ProbabilisticTheory :=
  classical (lp.measurableSubalgebra X)

/-- An event is a measurable set of configurations. -/
abbrev Event (X : Type*) [MeasurableSpace X] : Type _ := {s : Set X // MeasurableSet s}

variable {X : Type*} [MeasurableSpace X]

/-- The union of countably many events. -/
def Event.iUnion {ι : Sort*} [Countable ι] (s : ι → Event X) : Event X :=
  ⟨⋃ i, (s i : Set X), .iUnion fun i ↦ (s i).2⟩

@[simp] lemma Event.coe_iUnion {ι : Sort*} [Countable ι] (s : ι → Event X) :
    (Event.iUnion s : Set X) = ⋃ i, (s i : Set X) := rfl

/-- The value of an observable depends measurably on the configuration. -/
lemma measurable_coe (f : Observables (measurable X)) : Measurable f :=
  RCLike.measurable_re.comp (toSelfAdjoint f).1.2

/-- The values of an observable are bounded. -/
lemma exists_abs_le (f : Observables (measurable X)) : ∃ C, ∀ x, |f x| ≤ C :=
  ⟨_, fun x ↦ (Complex.abs_re_le_norm _).trans
    (lp.norm_apply_le_norm ENNReal.top_ne_zero (toSelfAdjoint f).1.1 x)⟩

/-- A bounded measurable real function as an observable. -/
noncomputable def ofFun (f : X → ℝ) (hf : Measurable f) (hb : ∃ C, ∀ x, |f x| ≤ C) :
    Observables (measurable X) :=
  toSelfAdjoint.symm ⟨⟨⟨Complex.ofReal ∘ f, memℓp_infty (hb.imp fun _ hC ↦ by
      rintro _ ⟨x, rfl⟩
      simpa using hC x)⟩, RCLike.measurable_ofReal.comp hf⟩,
    Subtype.ext (lp.ext (funext fun x ↦ Complex.conj_ofReal (f x)))⟩

@[simp] lemma coe_ofFun (f : X → ℝ) (hf : Measurable f) (hb) : ⇑(ofFun f hf hb) = f := rfl

/-! ## B. Suprema of countable families -/

variable {ι : Type*} [Countable ι] [Nonempty ι]

/-- The pointwise supremum of countably many observables bounded above is again an observable. -/
lemma exists_isLUB_range_apply {f : ι → Observables (measurable X)} {g : Observables (measurable X)}
    (hfg : ∀ i, f i ≤ g) : ∃ s : Observables (measurable X), ∀ x, IsLUB (range (f · x)) (s x) := by
  obtain ⟨C₀, h₀⟩ := exists_abs_le (f (Classical.arbitrary ι))
  obtain ⟨C₁, h₁⟩ := exists_abs_le g
  have hb x : BddAbove (range (f · x)) := ⟨g x, forall_mem_range.mpr fun n ↦ le_def.mp (hfg n) x⟩
  refine ⟨ofFun _ (.iSup fun n ↦ measurable_coe (f n)) ⟨max C₀ C₁, fun x ↦ ?_⟩,
    fun x ↦ isLUB_ciSup (hb x)⟩
  exact (abs_le_max_abs_abs (le_ciSup (hb x) _) (ciSup_le fun n ↦ le_def.mp (hfg n) x)).trans
    (max_le_max (h₀ x) (h₁ x))

/-- The least upper bound of countably many observables is their pointwise supremum. -/
lemma isLUB_range_apply {f : ι → Observables (measurable X)} {g : Observables (measurable X)}
    (h : IsLUB (range f) g) (x : X) : IsLUB (range (f · x)) (g x) := by
  obtain ⟨s, hs⟩ := exists_isLUB_range_apply fun n ↦ h.1 ⟨n, rfl⟩
  exact h.unique (isLUB_range_of_apply hs) ▸ hs x

end ProbabilisticTheory.Classical
