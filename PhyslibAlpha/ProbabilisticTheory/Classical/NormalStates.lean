/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.Classical.BoundedMeasurable
public import PhyslibAlpha.ProbabilisticTheory.Channel.Normal
public import PhyslibAlpha.ProbabilisticTheory.Classical.LatticeObservables
public import PhyslibAlpha.ProbabilisticTheory.Measurement.BornRule

/-!
# States of a classical system

## i. Overview

Each outcome `x` gives the deterministic state `f ↦ f x`, which predicts every observable with
certainty; deterministic states are normal and pure.

In a normal state, the effect-valued measure of the outcome has a probability measure on `Ω` as
outcome distribution. Conversely, integrating against a probability measure is a normal state.
These are inverse to each other: the normal states of a classical system are exactly the
probability measures on its outcomes.

## ii. Key results

- `BoundedMeasurable.eval` : the deterministic state at an outcome.
- `BoundedMeasurable.isPure_eval` : deterministic states are pure.
- `BoundedMeasurable.ofMeasure` : the state given by integrating against a probability measure.
- `BoundedMeasurable.toMeasure` : the outcome distribution of a normal state.
- `BoundedMeasurable.normalStateEquiv` : the normal states are the probability measures.

## iii. Table of contents

- A. Deterministic states
- B. Purity
- C. From measures to states
- D. From states to measures
- E. The correspondence

-/

@[expose] public section

namespace BoundedMeasurable
open ProbabilisticTheory

open UnitalPositiveLinearMap

variable {Ω : Type*} [MeasurableSpace Ω]

/-!

## A. Deterministic states

-/

/-- The deterministic state at the outcome `x`. -/
def eval (x : Ω) : 𝓢[ℝ, BoundedMeasurable Ω] :=
  ofLinearMap ⟨⟨fun f => f x, fun _ _ => rfl⟩, fun _ _ => rfl⟩ (fun _ hf => le_def.1 hf x) rfl

@[simp] lemma eval_apply (x : Ω) (f : BoundedMeasurable Ω) : eval x f = f x := rfl

lemma isNormal_eval (x : Ω) : (eval x).IsNormal := fun _ _ _ hg =>
  isLUB_range_iff.1 hg x

/-!

## B. Purity

-/

/-- Deterministic states are pure: the value of the smaller of two observables at `x` is the
smaller value. -/
lemma isPure_eval (x : Ω) : (eval x).IsPure :=
  isPure_iff_map_inf.2 fun _ _ => rfl

end BoundedMeasurable

namespace BoundedMeasurable
open ProbabilisticTheory

open UnitalPositiveLinearMap MeasureTheory Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω]

/-!

## C. From measures to states

-/

/-- A state is bounded by any pointwise bound of an observable. -/
lemma abs_apply_le (ω : 𝓢[ℝ, BoundedMeasurable Ω]) {g : BoundedMeasurable Ω} {ε : ℝ}
    (hg : ∀ x, |g x| ≤ ε) : |ω g| ≤ ε := by
  have h1 := map_nonneg ω (show 0 ≤ ε • 1 - g from le_def.2 fun x => by
    simpa using (le_abs_self _).trans (hg x))
  have h2 := map_nonneg ω (show 0 ≤ ε • 1 + g from le_def.2 fun x => by
    simpa [neg_le_iff_add_nonneg'] using (neg_abs_le _).trans' (neg_le_neg (hg x)))
  simp only [map_sub, map_add, map_smul, map_one, smul_eq_mul, mul_one] at h1 h2
  exact abs_le.2 ⟨by linarith, by linarith⟩

/-- Integration against a probability measure, as a state. -/
noncomputable def ofMeasure (μ : ProbabilityMeasure Ω) : 𝓢[ℝ, BoundedMeasurable Ω] :=
  ofLinearMap ⟨⟨fun f => ∫ x, f x ∂(μ : Measure Ω), fun f g =>
    integral_add (f.integrable _) (g.integrable _)⟩, fun c f => integral_const_mul c _⟩
    (fun _ hf => integral_nonneg (le_def.1 hf))
    (by change ∫ x, (1 : BoundedMeasurable Ω) x ∂(μ : Measure Ω) = 1; simp)

@[simp] lemma ofMeasure_apply (μ : ProbabilityMeasure Ω) (f : BoundedMeasurable Ω) :
    ofMeasure μ f = ∫ x, f x ∂(μ : Measure Ω) := rfl

/-- Integration against a probability measure is normal, by dominated convergence. -/
lemma isNormal_ofMeasure (μ : ProbabilityMeasure Ω) : (ofMeasure μ).IsNormal := fun f g hf hg => by
  obtain ⟨C, hC⟩ := (f 0).exists_bound
  obtain ⟨D, hD⟩ := g.exists_bound
  have hle n x : |f n x| ≤ C + D := by
    have h1 := le_def.1 (hf (Nat.zero_le n)) x
    have h2 := le_def.1 (hg.1 ⟨n, rfl⟩) x
    refine abs_le.2 ⟨?_, ?_⟩ <;> linarith [neg_abs_le (f 0 x), hC x, abs_nonneg (g x), hD x,
      le_abs_self (g x), abs_nonneg (f 0 x)]
  refine isLUB_of_tendsto_atTop (fun m n hmn => integral_mono ((f m).integrable _)
    ((f n).integrable _) (le_def.1 (hf hmn))) ?_
  exact tendsto_integral_of_dominated_convergence (fun _ => C + D)
    (fun n => (f n).measurable.aestronglyMeasurable) (integrable_const _)
    (fun n => .of_forall (hle n)) (.of_forall fun x => tendsto_atTop_isLUB
      (fun m n hmn => le_def.1 (hf hmn) x) (isLUB_range_iff.1 hg x))

/-!

## D. From states to measures

-/

/-- The outcome distribution of a normal state. -/
noncomputable def toMeasure (ω : 𝓢[ℝ, BoundedMeasurable Ω]) (hω : ω.IsNormal) :
    ProbabilityMeasure Ω :=
  outcomeMeasurement.probabilityLaw ω hω

lemma toMeasure_apply (ω : 𝓢[ℝ, BoundedMeasurable Ω]) (hω : ω.IsNormal) {s : Set Ω}
    (hs : MeasurableSet s) :
    (toMeasure ω hω : Measure Ω) s = ENNReal.ofReal (ω (indicator s hs)) :=
  EffectValuedMeasure.probabilityLaw_apply _ _ _ s hs

lemma measureReal_toMeasure (ω : 𝓢[ℝ, BoundedMeasurable Ω]) (hω : ω.IsNormal) {s : Set Ω}
    (hs : MeasurableSet s) :
    (toMeasure ω hω : Measure Ω).real s = ω (indicator s hs) := by
  rw [measureReal_def, toMeasure, EffectValuedMeasure.probabilityLaw_apply _ _ _ s hs]
  exact ENNReal.toReal_ofReal (map_nonneg ω (indicatorEffect s hs).2.1)

lemma toMeasure_ofMeasure (μ : ProbabilityMeasure Ω) :
    toMeasure (ofMeasure μ) (isNormal_ofMeasure μ) = μ :=
  ProbabilityMeasure.toMeasure_injective <| Measure.ext fun s hs => by
    rw [← ofReal_measureReal, measureReal_toMeasure _ _ hs, ofMeasure_apply]
    simp [integral_indicator_one hs]

/-!

## E. The correspondence

-/

/-- Integration against the outcome distribution agrees with the normal state on indicators, hence
on staircases. -/
lemma ofMeasure_toMeasure_staircase (ω : 𝓢[ℝ, BoundedMeasurable Ω]) (hω : ω.IsNormal)
    (g : BoundedMeasurable Ω) (N K : ℕ) :
    ofMeasure (toMeasure ω hω) (staircase g N K) = ω (staircase g N K) := by
  simp only [staircase, map_sum, map_smul]
  refine Finset.sum_congr rfl fun k _ => congrArg _ ?_
  rw [ofMeasure_apply]
  simp only [BoundedMeasurable.indicator_apply]
  rw [integral_indicator_one (measurableSet_le measurable_const g.measurable),
    measureReal_toMeasure]

lemma ofMeasure_toMeasure_apply_of_nonneg (ω : 𝓢[ℝ, BoundedMeasurable Ω]) (hω : ω.IsNormal)
    {g : BoundedMeasurable Ω} (h0 : 0 ≤ g) {K : ℕ} (hK : ∀ x, g x ≤ K) :
    ofMeasure (toMeasure ω hω) g = ω g := by
  refine sub_eq_zero.1 (abs_nonpos_iff.1 (le_of_forall_pos_le_add fun ε hε => ?_))
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / ε)
  have hNpos : 0 < N := Nat.cast_pos.1 ((div_pos two_pos hε).trans hN)
  have h1 := abs_apply_le (ofMeasure (toMeasure ω hω)) (abs_sub_staircase_le hNpos h0 hK)
  have h2 := abs_apply_le ω (abs_sub_staircase_le hNpos h0 hK)
  rw [map_sub, ofMeasure_toMeasure_staircase] at h1
  rw [map_sub] at h2
  have : 2 * (N : ℝ)⁻¹ < ε := by
    rw [← div_eq_mul_inv, div_lt_iff₀ (Nat.cast_pos.2 hNpos)]; rwa [div_lt_iff₀ hε, mul_comm] at hN
  linarith [abs_sub_le (ofMeasure (toMeasure ω hω) g) (ω (staircase g N K)) (ω g),
    abs_sub_comm (ω g) (ω (staircase g N K))]

/-- A normal state is integration against its outcome distribution. -/
lemma ofMeasure_toMeasure (ω : 𝓢[ℝ, BoundedMeasurable Ω]) (hω : ω.IsNormal) :
    ofMeasure (toMeasure ω hω) = ω := by
  refine UnitalPositiveLinearMap.ext fun f => ?_
  obtain ⟨C, hC⟩ := f.exists_bound
  have h0 : 0 ≤ f + C • 1 := le_def.2 fun x => by
    have := neg_abs_le (f x)
    have := hC x
    simp only [BoundedMeasurable.zero_apply, BoundedMeasurable.add_apply,
      BoundedMeasurable.smul_apply, BoundedMeasurable.one_apply, mul_one]
    linarith
  have h := ofMeasure_toMeasure_apply_of_nonneg ω hω h0 (K := ⌈2 * C⌉₊) fun x => by
    simp only [BoundedMeasurable.add_apply, BoundedMeasurable.smul_apply,
      BoundedMeasurable.one_apply, mul_one]
    linarith [le_abs_self (f x), hC x, Nat.le_ceil (2 * C)]
  simpa [map_add, map_smul] using h

/-- **The normal states of a classical system are the probability measures on its outcomes.** -/
noncomputable def normalStateEquiv :
    {ω : 𝓢[ℝ, BoundedMeasurable Ω] // ω.IsNormal} ≃ ProbabilityMeasure Ω where
  toFun ω := toMeasure ω.1 ω.2
  invFun μ := ⟨ofMeasure μ, isNormal_ofMeasure μ⟩
  left_inv ω := Subtype.ext (ofMeasure_toMeasure ω.1 ω.2)
  right_inv μ := toMeasure_ofMeasure μ

end BoundedMeasurable

