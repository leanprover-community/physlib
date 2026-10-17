/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Mathematics.Convex.Choquet.Mixture
public import Mathlib.MeasureTheory.Measure.DiracProba
public import Mathlib.MeasureTheory.Measure.Prokhorov

/-!
# Representing measures and the Choquet order

Representing measures of points of a convex set, the Choquet order, and maximal measures.

## i. Overview

A probability measure on a convex set `S` represents a point `x` when `x` is its average: every
continuous linear functional takes at `x` its average value under the measure. For states, a
representing measure is a way to prepare the state as a random mixture.

A point has many representing measures, the Dirac measure at the point being the trivial one. One
measure is higher than another in the Choquet order when it gives every continuous convex function a
larger average. Higher measures push their weight further out, towards the extreme points. On a
compact set every point has a representing measure that is maximal in this order.

## ii. Key results

- `Choquet.IsRepresentingMeasure` states that a probability measure represents a point.
- `Choquet.ChoquetLE` is the Choquet order.
- `Choquet.ChoquetLE.isRepresentingMeasure` proves that a higher measure represents the same point.
- `Choquet.exists_isChoquetMaximalAt` proves that every point has a maximal representing measure.

## iii. Table of contents

- A. Representing measures
- B. The Choquet order
- C. Maximal representing measures

## iv. References

* None.

-/

@[expose] public section

open MeasureTheory Filter Topology Set

namespace Choquet

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] {S : Set V}
  (hS : Convex ℝ S) [CompactSpace S] [MeasurableSpace S] [BorelSpace S]

/-!

## A. Representing measures

-/

/-- A probability measure represents `x` when every continuous linear functional has the same
value at `x` as its integral. -/
def IsRepresentingMeasure (x : S) (μ : ProbabilityMeasure S) : Prop :=
  ∀ ℓ : V →L[ℝ] ℝ, ℓ x = ∫ y, ℓ y ∂(μ : Measure S)

/-- The probability measures representing `x`. -/
def representingMeasures (x : S) : Set (ProbabilityMeasure S) :=
  {μ | IsRepresentingMeasure x μ}

/-- A continuous linear functional, as a continuous function on `S`. -/
def restrictCLM (ℓ : V →L[ℝ] ℝ) : C(S, ℝ) :=
  ⟨fun y => ℓ y, ℓ.continuous.comp continuous_subtype_val⟩

lemma isClosed_representingMeasures (x : S) : IsClosed (representingMeasures x) := by
  simp only [representingMeasures, IsRepresentingMeasure, Set.ofPred_forall]
  exact isClosed_iInter fun ℓ => isClosed_eq continuous_const
    (ProbabilityMeasure.continuous_integral_continuousMap (restrictCLM ℓ))

/-!

## B. The Choquet order

-/

/-- The Choquet order: `ν` gives every continuous convex function at least the integral `μ`
gives it. -/
def ChoquetLE (μ ν : ProbabilityMeasure S) : Prop :=
  ∀ f : C(S, ℝ), IsConvexFunction hS f → ∫ x, f x ∂(μ : Measure S) ≤ ∫ x, f x ∂(ν : Measure S)

omit [CompactSpace S] [BorelSpace S] in
@[refl] lemma ChoquetLE.refl (μ : ProbabilityMeasure S) : ChoquetLE hS μ μ := fun _ _ => le_rfl

omit [CompactSpace S] [BorelSpace S] in
lemma ChoquetLE.trans {μ ν ρ : ProbabilityMeasure S} (hμν : ChoquetLE hS μ ν)
    (hνρ : ChoquetLE hS ν ρ) : ChoquetLE hS μ ρ :=
  fun f hf => (hμν f hf).trans (hνρ f hf)

lemma isClosed_setOf_choquetLE (μ : ProbabilityMeasure S) :
    IsClosed {ν : ProbabilityMeasure S | ChoquetLE hS μ ν} := by
  simp only [ChoquetLE, Set.ofPred_forall]
  exact isClosed_iInter fun f => isClosed_iInter fun _ =>
    isClosed_le continuous_const (ProbabilityMeasure.continuous_integral_continuousMap f)

omit [CompactSpace S] [BorelSpace S] in
/-- Moving up the Choquet order keeps the represented point. -/
lemma ChoquetLE.isRepresentingMeasure {x : S} {μ ν : ProbabilityMeasure S}
    (hμ : IsRepresentingMeasure x μ) (hμν : ChoquetLE hS μ ν) : IsRepresentingMeasure x ν :=
  fun ℓ => (hμ ℓ).trans <| le_antisymm (hμν (restrictCLM ℓ) (isConvexFunction_apply hS ℓ)) <| by
    simpa [restrictCLM, integral_neg] using hμν (restrictCLM (-ℓ)) (isConvexFunction_apply hS (-ℓ))

/-!

## C. Maximal representing measures

-/

variable [T2Space S]

omit [CompactSpace S] in
lemma representingMeasures_nonempty (x : S) : (representingMeasures x).Nonempty :=
  ⟨diracProba x, fun ℓ => (integral_dirac (fun y : S => ℓ y) x).symm⟩

/-- `μ` represents `x` and is maximal in the Choquet order among the measures representing `x`. -/
def IsChoquetMaximalAt (x : S) (μ : ProbabilityMeasure S) : Prop :=
  IsRepresentingMeasure x μ ∧ ∀ ν ∈ representingMeasures x, ChoquetLE hS μ ν → ChoquetLE hS ν μ

omit [CompactSpace S] [BorelSpace S] [T2Space S] in
/-- The representing measures above the members of a chain form a directed family. -/
lemma directed_choquetUpperSets (x : S) {c : Set (representingMeasures x)}
    (hc : IsChain (fun a b : representingMeasures x => ChoquetLE hS a.1 b.1) c) :
    Directed (· ⊇ ·) fun i : c => representingMeasures x ∩ {ν | ChoquetLE hS i.1.1 ν} :=
  fun i j => by
    rcases eq_or_ne i j with rfl | hij
    · exact ⟨i, le_rfl, le_rfl⟩
    rcases hc i.2 j.2 (Subtype.coe_injective.ne hij) with h | h
    · exact ⟨j, fun ν hν => ⟨hν.1, (ChoquetLE.trans hS h hν.2)⟩, le_rfl⟩
    · exact ⟨i, le_rfl, fun ν hν => ⟨hν.1, ChoquetLE.trans hS h hν.2⟩⟩

/-- A nonempty chain of measures representing `x` has an upper bound among them. -/
lemma exists_choquetLE_of_isChain (x : S) {c : Set (representingMeasures x)}
    (hc : IsChain (fun a b : representingMeasures x => ChoquetLE hS a.1 b.1) c)
    (hcne : c.Nonempty) : ∃ ub : representingMeasures x, ∀ a ∈ c, ChoquetLE hS a.1 ub.1 := by
  have : Nonempty c := hcne.to_subtype
  have htcl (i : c) : IsClosed (representingMeasures x ∩ {ν | ChoquetLE hS i.1.1 ν}) :=
    (isClosed_representingMeasures x).inter (isClosed_setOf_choquetLE hS _)
  obtain ⟨ν, hν⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed _
    (directed_choquetUpperSets hS x hc) (fun i => ⟨i.1, i.1.2, ChoquetLE.refl hS _⟩)
    (fun i => (htcl i).isCompact) htcl
  obtain ⟨i₀⟩ := ‹Nonempty c›
  exact ⟨⟨ν, (Set.mem_iInter.mp hν i₀).1⟩, fun a ha => (Set.mem_iInter.mp hν ⟨a, ha⟩).2⟩

/-- Every point has a Choquet-maximal representing measure. -/
lemma exists_isChoquetMaximalAt (x : S) :
    ∃ μ : ProbabilityMeasure S, IsChoquetMaximalAt hS x μ := by
  obtain ⟨m, hm⟩ := exists_maximal_of_chains_bounded
    (r := fun a b : representingMeasures x => ChoquetLE hS a.1 b.1)
    (fun c hc => c.eq_empty_or_nonempty.elim
      (fun h => ⟨⟨_, (representingMeasures_nonempty x).some_mem⟩, fun a ha => by simp [h] at ha⟩)
      (exists_choquetLE_of_isChain hS x hc))
    (fun hab hbc => ChoquetLE.trans hS hab hbc)
  exact ⟨m, m.2, fun ν hν hmν => hm ⟨ν, hν⟩ hmν⟩

end Choquet
