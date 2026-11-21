/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.ClassicalMechanics.Observables.Dirac
public import Physlib.Mathematics.ForMathlib.Indicator
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
public import Mathlib.MeasureTheory.Function.SimpleFunc
public import Mathlib.MeasureTheory.Function.SpecialFunctions.RCLike
public import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Measurable classical observables

Dirac states are normal on the bounded measurable observables of a classical system.

## i. Overview

A configuration space with a σ-algebra of events has the bounded measurable real functions as
observables. They form a closed subalgebra of the bounded functions. Observables, Dirac states
and purity therefore come from the general construction.

The supremum of an increasing sequence of observables is taken configuration by configuration.
Every Dirac state therefore preserves such suprema, which makes it normal. Two kinds of
increasing sequences matter for statistics. The indicators of disjoint events add up to the
indicator of their union, which becomes countable additivity of probabilities. Every positive
observable is the supremum of an increasing sequence of simple observables, which are finite
combinations of event indicators.

## ii. Key results

- `ProbabilisticTheory.ClassicalObservable` : bounded measurable classical observables.
- `ProbabilisticTheory.ClassicalState` : states of classical systems.
- `ProbabilisticTheory.Classical.isLUB_range_iff` : suprema of sequences of observables are taken
  at each configuration.
- `ProbabilisticTheory.Classical.isNormal_dirac` : Dirac states are normal.
- `ProbabilisticTheory.Classical.indicator` : the observable asking whether an event occurred.
- `ProbabilisticTheory.Classical.isLUB_sum_indicator` : indicators of disjoint events add up to the
  indicator of their union.
- `ProbabilisticTheory.Classical.isLUB_approx` : positive observables are suprema of simple
  observables.

## iii. Table of contents

- A. Bounded measurable functions
- B. Suprema of sequences
- C. Events
- D. Simple observables

## iv. References

-/

@[expose] public section

open Set MeasureTheory
open scoped ENNReal

namespace ProbabilisticTheory.Classical

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## A. Bounded measurable functions -/

/-- The bounded measurable complex functions on `Ω`. -/
noncomputable def measurableAlgebra (Ω : Type*) [MeasurableSpace Ω] :
    StarSubalgebra ℂ (lp (fun _ : Ω ↦ ℂ) ∞) where
  carrier := {f | Measurable (f : Ω → ℂ)}
  zero_mem' := measurable_const
  one_mem' := measurable_const
  add_mem' := Measurable.add
  mul_mem' := Measurable.mul
  algebraMap_mem' _ := measurable_const
  star_mem' hf := continuous_star.measurable.comp hf

/-- Uniform limits of bounded measurable functions are measurable. -/
instance isClosed_measurableAlgebra :
    IsClosed (measurableAlgebra Ω : Set (lp (fun _ : Ω ↦ ℂ) ∞)) :=
  IsSeqClosed.isClosed fun _ g hf hg ↦ measurable_of_tendsto_metrizable hf
    (tendsto_pi_nhds.mpr fun x ↦ ((lp.evalCLM ℂ (fun _ : Ω ↦ ℂ) ∞ x).continuous.tendsto g).comp hg)

/-- A bounded measurable real observable on the configuration space `Ω`. -/
noncomputable abbrev _root_.ProbabilisticTheory.ClassicalObservable (Ω : Type*)
    [MeasurableSpace Ω] :=
  selfAdjoint (measurableAlgebra Ω)

/-- A state of a classical system with bounded measurable observables. -/
abbrev _root_.ProbabilisticTheory.ClassicalState (Ω : Type*) [MeasurableSpace Ω] :=
  (ofCStarAlgebra (measurableAlgebra Ω)).State

/-- The value of an observable depends measurably on the configuration. -/
lemma measurable_toFun (f : ClassicalObservable Ω) : Measurable (toFun f) :=
  RCLike.measurable_re.comp f.val.property

/-- The values of an observable are bounded by its norm. -/
lemma abs_toFun_le_norm (f : ClassicalObservable Ω) (x : Ω) :
    |toFun f x| ≤ ‖(f : measurableAlgebra Ω)‖ :=
  (Complex.abs_re_le_norm _).trans (lp.norm_apply_le_norm ENNReal.top_ne_zero f.val.val x)

/-- Every observable is integrable for a finite measure on configurations. -/
lemma integrable_toFun (f : ClassicalObservable Ω) (μ : Measure Ω) [IsFiniteMeasure μ] :
    Integrable (toFun f) μ :=
  .of_bound (measurable_toFun f).aestronglyMeasurable _ (.of_forall (abs_toFun_le_norm f))

/-- A bounded measurable real function as a classical observable. -/
noncomputable def ofFun (f : Ω → ℝ) (hf : Measurable f) (hb : ∃ C, ∀ x, |f x| ≤ C) :
    ClassicalObservable Ω :=
  ⟨⟨⟨Complex.ofReal ∘ f, memℓp_infty (hb.imp fun _ hC ↦ by
      rintro _ ⟨x, rfl⟩
      simpa using hC x)⟩, RCLike.measurable_ofReal.comp hf⟩,
    Subtype.ext (lp.ext (funext fun x ↦ Complex.conj_ofReal (f x)))⟩

@[simp]
lemma toFun_ofFun (f : Ω → ℝ) (hf : Measurable f) (hb) : toFun (ofFun f hf hb) = f := rfl

/-! ## B. Suprema of sequences -/

/-- The values of a sequence of observables below a common bound are bounded above. -/
lemma bddAbove_range_toFun {f : ℕ → ClassicalObservable Ω} {g : ClassicalObservable Ω}
    (hfg : ∀ n, f n ≤ g) (x : Ω) : BddAbove (range fun n ↦ toFun (f n) x) :=
  ⟨toFun g x, forall_mem_range.mpr fun n ↦ toFun_le_toFun_iff.mpr (hfg n) x⟩

/-- The pointwise supremum of a sequence of observables below a common bound is an
observable. -/
lemma exists_toFun_eq_iSup {f : ℕ → ClassicalObservable Ω} {g : ClassicalObservable Ω}
    (hfg : ∀ n, f n ≤ g) : ∃ s : ClassicalObservable Ω, ∀ x, toFun s x = ⨆ n, toFun (f n) x :=
  ⟨ofFun _ (Measurable.iSup fun n ↦ measurable_toFun (f n))
    ⟨max ‖(f 0 : measurableAlgebra Ω)‖ ‖(g : measurableAlgebra Ω)‖, fun x ↦
      (abs_le_max_abs_abs (le_ciSup (bddAbove_range_toFun hfg x) 0)
        (ciSup_le fun n ↦ toFun_le_toFun_iff.mpr (hfg n) x)).trans
        (max_le_max (abs_toFun_le_norm (f 0) x) (abs_toFun_le_norm g x))⟩, fun _ ↦ rfl⟩

/-- An observable whose value is the supremum of the values of a sequence at every configuration
is the supremum of the sequence. -/
lemma isLUB_of_forall_isLUB_toFun {f : ℕ → ClassicalObservable Ω} {g : ClassicalObservable Ω}
    (h : ∀ x, IsLUB (range fun n ↦ toFun (f n) x) (toFun g x)) : IsLUB (range f) g :=
  ⟨forall_mem_range.mpr fun n ↦ toFun_le_toFun_iff.mp fun x ↦ (h x).1 ⟨n, rfl⟩,
    fun _ hb ↦ toFun_le_toFun_iff.mp fun x ↦
      (h x).2 (forall_mem_range.mpr fun n ↦ toFun_le_toFun_iff.mpr (hb ⟨n, rfl⟩) x)⟩

/-- An observable is the supremum of a sequence exactly when its value is the supremum of the
values at every configuration. -/
lemma isLUB_range_iff {f : ℕ → ClassicalObservable Ω} {g : ClassicalObservable Ω} :
    IsLUB (range f) g ↔ ∀ x, IsLUB (range fun n ↦ toFun (f n) x) (toFun g x) := by
  refine ⟨fun h x ↦ ?_, isLUB_of_forall_isLUB_toFun⟩
  have hfg n : f n ≤ g := h.1 ⟨n, rfl⟩
  obtain ⟨s, hs⟩ := exists_toFun_eq_iSup hfg
  have hgs : g ≤ s := h.2 (forall_mem_range.mpr fun n ↦ toFun_le_toFun_iff.mp fun y ↦
    (hs y).symm ▸ le_ciSup (bddAbove_range_toFun hfg y) n)
  exact ⟨forall_mem_range.mpr fun n ↦ toFun_le_toFun_iff.mpr (hfg n) x, fun _ hb ↦
    (toFun_le_toFun_iff.mpr hgs x).trans ((hs x).symm ▸ ciSup_le fun n ↦ hb ⟨n, rfl⟩)⟩

/-- Dirac states are normal. -/
lemma isNormal_dirac (x : Ω) : (dirac x : ClassicalState Ω).IsNormal :=
  fun _ _ _ hg ↦ isLUB_range_iff.mp hg x

/-! ## C. Events -/

/-- The indicator observable of an event, with value `1` in the event and `0` outside. -/
noncomputable def indicator (s : Set Ω) (hs : MeasurableSet s) : ClassicalObservable Ω :=
  ofFun (s.indicator 1) (measurable_one.indicator hs)
    ⟨1, fun x ↦ by by_cases hx : x ∈ s <;> simp [hx]⟩

@[simp]
lemma toFun_indicator (s : Set Ω) (hs : MeasurableSet s) :
    toFun (indicator s hs) = s.indicator 1 := rfl

/-- Event indicators are positive observables. -/
lemma indicator_nonneg (s : Set Ω) (hs : MeasurableSet s) : 0 ≤ indicator s hs :=
  toFun_le_toFun_iff.mp fun x ↦ show (0 : ℝ) ≤ s.indicator 1 x from
    Set.indicator_nonneg (fun _ _ ↦ zero_le_one) x

@[simp]
lemma indicator_empty : indicator (∅ : Set Ω) .empty = 0 :=
  toFun_injective (Set.indicator_empty _)

@[simp]
lemma indicator_univ : indicator (univ : Set Ω) .univ = 1 :=
  toFun_injective (Set.indicator_univ _)

/-- The indicators of disjoint events add up to the indicator of their union. -/
lemma isLUB_sum_indicator {s : ℕ → Set Ω} (hs : ∀ n, MeasurableSet (s n))
    (hd : Pairwise (Function.onFun Disjoint s)) :
    IsLUB (range fun N ↦ ∑ n ∈ Finset.range N, indicator (s n) (hs n))
      (indicator (⋃ n, s n) (.iUnion hs)) :=
  isLUB_range_iff.mpr fun x ↦ by
    simpa [map_sum] using Set.isLUB_sum_indicator_iUnion zero_le_one hd x

/-- Events distinguish configurations: different configurations give different Dirac states. -/
lemma dirac_injective [MeasurableSingletonClass Ω] :
    Function.Injective (dirac : Ω → ClassicalState Ω) := fun x y h ↦ by
  have := DFunLike.congr_fun h (indicator {y} (.singleton y))
  rw [dirac_apply, dirac_apply, toFun_indicator, Set.indicator_of_mem (mem_singleton y)] at this
  by_contra hxy
  rw [Set.indicator_of_notMem (mt mem_singleton_iff.mp hxy)] at this
  exact zero_ne_one this

/-! ## D. Simple observables -/

/-- Simple functions are classical observables. -/
noncomputable def ofSimpleFunc : SimpleFunc Ω ℝ →ₗ[ℝ] ClassicalObservable Ω where
  toFun f := ofFun f f.measurable (f.map abs).exists_forall_le
  map_add' _ _ := toFun_injective rfl
  map_smul' c f := toFun_injective (by rw [map_smul]; rfl)

@[simp]
lemma toFun_ofSimpleFunc (f : SimpleFunc Ω ℝ) : toFun (ofSimpleFunc f) = f := rfl

/-- Simple observables are finite combinations of event indicators. -/
lemma ofSimpleFunc_mem_span (f : SimpleFunc Ω ℝ) :
    ofSimpleFunc f ∈ Submodule.span ℝ {indicator s hs | (s : Set Ω) (hs : MeasurableSet s)} := by
  induction f using SimpleFunc.induction with
  | @const c s hs =>
    have h : ofSimpleFunc (.piecewise s hs (.const Ω c) (.const Ω 0)) = c • indicator s hs :=
      toFun_injective (funext fun x ↦ by by_cases hx : x ∈ s <;> simp [hx])
    exact h ▸ Submodule.smul_mem _ c (Submodule.subset_span ⟨s, hs, rfl⟩)
  | @add f g _ hf hg => exact (map_add ofSimpleFunc f g) ▸ Submodule.add_mem _ hf hg

/-- Mathlib's increasing simple approximations of a positive observable. -/
noncomputable def approx (f : ClassicalObservable Ω) (n : ℕ) : ClassicalObservable Ω :=
  ofSimpleFunc ((SimpleFunc.eapprox (ENNReal.ofReal ∘ toFun f) n).map ENNReal.toReal)

lemma monotone_approx (f : ClassicalObservable Ω) : Monotone (approx f) :=
  fun _ n hmn ↦ toFun_le_toFun_iff.mp fun x ↦ ENNReal.toReal_mono
    (SimpleFunc.eapprox_lt_top _ n x).ne (SimpleFunc.monotone_eapprox _ hmn x)

/-- A positive observable is the supremum of its increasing simple approximations. -/
lemma isLUB_approx {f : ClassicalObservable Ω} (hf : 0 ≤ f) : IsLUB (range (approx f)) f :=
  isLUB_range_iff.mpr fun x ↦ isLUB_of_tendsto_atTop
    (fun _ _ hmn ↦ toFun_le_toFun_iff.mpr (monotone_approx f hmn) x) (by
      simpa [approx, Function.comp_def, ENNReal.toReal_ofReal (toFun_le_toFun_iff.mpr hf x)] using
        (ENNReal.continuousAt_toReal ENNReal.ofReal_ne_top).tendsto.comp
          (SimpleFunc.tendsto_eapprox (measurable_toFun f).ennreal_ofReal x))

end ProbabilisticTheory.Classical
