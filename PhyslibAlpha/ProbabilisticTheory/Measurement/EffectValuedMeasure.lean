/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Physlib.ProbabilisticTheory.Effect.Complement
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Effect-valued measures

## i. Overview

An effect-valued measure with outcomes in `Ω` assigns to each event, a measurable set of outcomes,
an effect: the impossible event gets `0`, the certain event gets `1`, and the effects of disjoint
events add up, countably. Every measurement has one, sending an event to the effect testing whether
the outcome lands in it. For self-adjoint operators effect-valued measures are the POVMs.

On a finite discrete outcome space an effect-valued measure is the same as a family of effects
adding up to `1`, one for each outcome.

## ii. Key results

- `EffectValuedMeasure Ω E` : an effect-valued measure with outcomes in `Ω`.
- `EffectValuedMeasure.ofFintype` : the effect-valued measure of a normalized family of effects.
- `EffectValuedMeasure.map_union_of_disjoint` : additivity on two disjoint events.
- `EffectValuedMeasure.coe_apply_eq_atomSum` : on a finite outcome space, the effect of an event
  is the sum of the effects of its outcomes.
- `EffectValuedMeasure.mapOutcome` : relabeling outcomes along a measurable map.

## iii. Table of contents

- A. Effect-valued measures
- B. Atomic effect sums
- C. Finite-outcome effect-valued measures
- D. Finite additivity and atomic reconstruction
- E. Relabeling outcomes

-/

@[expose] public section

namespace ProbabilisticTheory

open Function

variable {Ω E : Type*} [MeasurableSpace Ω] [OrderUnitSpace E]

/-! ## A. Effect-valued measures -/

/-- An effect-valued measure: `∅ ↦ 0`, `univ ↦ 1`, countably additive. -/
structure EffectValuedMeasure (Ω : Type*) [MeasurableSpace Ω] (E : Type*) [OrderUnitSpace E] where
  /-- The effect assigned to each event. -/
  toFun : ∀ s : Set Ω, MeasurableSet s → Effect E
  /-- The impossible event gets `0`. -/
  map_empty' : toFun ∅ .empty = 0
  /-- The certain event gets `1`. -/
  map_univ' : toFun .univ .univ = 1
  /-- The effects of countably many disjoint events add up to the effect of their union. -/
  countably_additive' : ∀ (s : ℕ → Set Ω) (hs : ∀ n, MeasurableSet (s n)),
    Pairwise (Disjoint on s) →
      IsLUB (Set.range fun N => ∑ n ∈ Finset.range N, (toFun (s n) (hs n) : E))
        (toFun (⋃ n, s n) (.iUnion hs) : E)

namespace EffectValuedMeasure

instance : CoeFun (EffectValuedMeasure Ω E) fun _ => ∀ s : Set Ω, MeasurableSet s → Effect E where
  coe μ := μ.toFun

@[ext]
lemma ext {μ ν : EffectValuedMeasure Ω E} (h : ∀ s hs, μ s hs = ν s hs) : μ = ν := by
  cases μ; cases ν; congr; exact funext fun s => funext (h s)

@[simp]
lemma map_empty (μ : EffectValuedMeasure Ω E) : μ ∅ .empty = 0 := μ.map_empty'

@[simp]
lemma map_univ (μ : EffectValuedMeasure Ω E) : μ .univ .univ = 1 := μ.map_univ'

lemma countably_additive (μ : EffectValuedMeasure Ω E) {s : ℕ → Set Ω}
    (hs : ∀ n, MeasurableSet (s n)) (hd : Pairwise (Disjoint on s)) :
    IsLUB (Set.range fun N => ∑ n ∈ Finset.range N, (μ (s n) (hs n) : E))
      (μ (⋃ n, s n) (.iUnion hs) : E) :=
  μ.countably_additive' s hs hd

end EffectValuedMeasure

namespace EffectValuedMeasure

variable {Ω E : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  [OrderUnitSpace E]

/-! ## B. Atomic effect sums -/

/-- The outcomes of `s` as a finite set. -/
noncomputable def eventFinset (s : Set Ω) : Finset Ω := by
  classical
  exact Finset.univ.filter (· ∈ s)

/-- The sum of the atomic effects belonging to an event. -/
noncomputable def atomSum (a : Ω → Effect E) (s : Set Ω) : E :=
  ∑ x ∈ eventFinset s, (a x : E)

omit [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
lemma atomSum_nonneg (a : Ω → Effect E) (s : Set Ω) : 0 ≤ atomSum a s := by
  exact Finset.sum_nonneg fun x _ => (a x).2.1

omit [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
lemma atomSum_mono (a : Ω → Effect E) {s t : Set Ω} (hst : s ⊆ t) :
    atomSum a s ≤ atomSum a t := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro x hx
    simp only [eventFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact hst hx
  · exact fun x _ _ => (a x).2.1

omit [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
lemma atomSum_univ (a : Ω → Effect E) : atomSum a Set.univ = ∑ x, (a x : E) := by
  simp [atomSum, eventFinset]

omit [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
lemma atomSum_partialSums (a : Ω → Effect E) (s : ℕ → Set Ω)
    (hd : Pairwise (Disjoint on s)) (N : ℕ) :
    (∑ n ∈ Finset.range N, atomSum a (s n)) = atomSum a (⋃ n < N, s n) := by
  classical
  let t : ℕ → Finset Ω := fun n => eventFinset (s n)
  have ht : Set.PairwiseDisjoint (↑(Finset.range N) : Set ℕ) t := by
    intro i hi j hj hij
    change Disjoint (t i) (t j)
    rw [Finset.disjoint_left]
    intro x hxi hxj
    exact Set.disjoint_left.1 (hd hij) (by simpa [t, eventFinset] using hxi)
      (by simpa [t, eventFinset] using hxj)
  unfold atomSum
  rw [← Finset.sum_biUnion ht]
  apply Finset.sum_congr
  · ext x
    simp [t, eventFinset]
  · intro x hx
    rfl

omit [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
/-- On a finite outcome space, the union of a sequence of events is already the union of an initial
segment. -/
lemma exists_partialUnion_eq_iUnion [Finite Ω] (s : ℕ → Set Ω) :
    ∃ N, ⋃ n < N, s n = ⋃ n, s n := by
  let P : ℕ →o Set Ω := ⟨fun N => ⋃ n < N, s n, fun _ _ h =>
    Set.biUnion_subset_biUnion_left fun _ hn => lt_of_lt_of_le hn h⟩
  obtain ⟨N, hN⟩ := WellFoundedGT.monotone_chain_condition P
  refine ⟨N, (Set.iUnion₂_subset fun n _ => Set.subset_iUnion s n).antisymm
    (Set.iUnion_subset fun n => ?_)⟩
  rw [show (⋃ k < N, s k) = P (max N (n + 1)) from hN _ (le_max_left _ _)]
  exact Set.subset_biUnion_of_mem (u := s) (by omega : n < max N (n + 1))

/-! ## C. Finite-outcome effect-valued measures -/

/-- A normalized finite family of atomic effects as an effect-valued measure. -/
noncomputable def ofFintype (a : Ω → Effect E) (ha : ∑ x, (a x : E) = 1) :
    EffectValuedMeasure Ω E where
  toFun s _ := ⟨atomSum a s, atomSum_nonneg a s, by
    rw [← ha, ← atomSum_univ]
    exact atomSum_mono a (Set.subset_univ s)⟩
  map_empty' := Subtype.ext (by simp [atomSum, eventFinset])
  map_univ' := Subtype.ext (atomSum_univ a |>.trans ha)
  countably_additive' s _ hd := by
    change IsLUB (Set.range fun n => ∑ k ∈ Finset.range n, atomSum a (s k))
      (atomSum a (⋃ k, s k))
    obtain ⟨N, hN⟩ := exists_partialUnion_eq_iUnion s
    have hpartial (n : ℕ) :
        (∑ k ∈ Finset.range n, atomSum a (s k)) =
          atomSum a (⋃ k < n, s k) := atomSum_partialSums a s hd n
    refine ⟨Set.forall_mem_range.2 fun n => ?_, fun b hb => ?_⟩
    · rw [hpartial]
      exact atomSum_mono a (Set.iUnion₂_subset fun k hk => Set.subset_iUnion s k)
    · apply hb
      refine ⟨N, ?_⟩
      change (∑ k ∈ Finset.range N, atomSum a (s k)) = atomSum a (⋃ k, s k)
      rw [hpartial, hN]

omit [MeasurableSingletonClass Ω] in
@[simp]
lemma coe_ofFintype_apply (a : Ω → Effect E) (ha : ∑ x, (a x : E) = 1)
    (s : Set Ω) (hs : MeasurableSet s) : ((ofFintype a ha) s hs : E) = atomSum a s :=
  rfl

omit [MeasurableSingletonClass Ω] in
@[simp, nolint simpNF]
lemma coe_ofFintype_singleton (a : Ω → Effect E) (ha : ∑ x, (a x : E) = 1) (x : Ω)
    (hx : MeasurableSet {x}) : ((ofFintype a ha) {x} hx : E) = a x := by
  rw [coe_ofFintype_apply, atomSum, show eventFinset ({x} : Set Ω) = {x} by
    ext; simp [eventFinset], Finset.sum_singleton]

/-! ## D. Finite additivity and atomic reconstruction -/

omit [Fintype Ω] [MeasurableSingletonClass Ω] in
/-- An effect-valued measure is additive on two disjoint events. -/
lemma map_union_of_disjoint (M : EffectValuedMeasure Ω E) {s t : Set Ω}
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hd : Disjoint s t) :
    (M (s ∪ t) (hs.union ht) : E) = M s hs + M t ht := by
  let u : ℕ → Set Ω := fun n => if n = 0 then s else if n = 1 then t else ∅
  have hu (n : ℕ) : MeasurableSet (u n) := by unfold u; split_ifs <;> simp [hs, ht]
  have hud : Pairwise (Disjoint on u) := fun i j hij => by
    simp only [Function.onFun, u]; split_ifs <;> simp_all [hd.symm]
  have hU : ⋃ n, u n = s ∪ t := by
    ext x; simp only [Set.mem_iUnion, Set.mem_union, u]
    exact ⟨fun ⟨n, hn⟩ => by split_ifs at hn <;> simp_all,
      fun h => h.elim (fun h => ⟨0, by simpa⟩) fun h => ⟨1, by simpa⟩⟩
  have hsum (n : ℕ) : ∑ k ∈ Finset.range (n + 2), (M (u k) (hu k) : E) = M s hs + M t ht := by
    simp [Finset.sum_range_succ', u, add_comm]
  have hmono : Monotone fun n => ∑ k ∈ Finset.range n, (M (u k) (hu k) : E) :=
    (Finset.sum_mono_set_of_nonneg fun k => (M (u k) (hu k)).2.1).comp Finset.range_mono
  have hlub := M.countably_additive hu hud
  simp only [hU] at hlub
  exact hlub.unique (IsGreatest.isLUB ⟨⟨2, hsum 0⟩, Set.forall_mem_range.2 fun n =>
    (hmono (Nat.le_add_right n 2)).trans (hsum n).le⟩)

omit [Fintype Ω] in
/-- The effect of a finite event is the sum of the effects of its outcomes. -/
lemma coe_apply_finset (M : EffectValuedMeasure Ω E) (t : Finset Ω) :
    (M t t.measurableSet : E) = ∑ x ∈ t, (M {x} (measurableSet_singleton x) : E) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | @insert x t hxt ih =>
    rw [Finset.sum_insert hxt, ← ih, ← map_union_of_disjoint M (measurableSet_singleton x)
      t.measurableSet (Set.disjoint_singleton_left.2 hxt)]
    simp only [Finset.coe_insert, Set.insert_eq]

/-- On a finite discrete outcome space, a measurement is the sum of its singleton effects. -/
lemma coe_apply_eq_atomSum (M : EffectValuedMeasure Ω E) (s : Set Ω) (hs : MeasurableSet s) :
    (M s hs : E) = atomSum (fun x => M {x} (measurableSet_singleton x)) s := by
  have hevent : (eventFinset s : Set Ω) = s := by ext; simp [eventFinset]
  rw [atomSum, ← coe_apply_finset]
  simp only [hevent]

/-- Two measurements on a finite discrete space agree when all singleton effects agree. -/
lemma ext_of_singleton {M N : EffectValuedMeasure Ω E}
    (h : ∀ x, M {x} (measurableSet_singleton x) = N {x} (measurableSet_singleton x)) :
    M = N := by
  apply EffectValuedMeasure.ext
  intro s hs
  apply Subtype.ext
  rw [coe_apply_eq_atomSum M s hs, coe_apply_eq_atomSum N s hs]
  congr 1
  funext x
  exact h x

end EffectValuedMeasure

namespace EffectValuedMeasure

variable {Ω Ω' E : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [OrderUnitSpace E]

/-! ## E. Relabeling outcomes -/

/-- Relabel the outcomes of an effect-valued measure along a measurable map. -/
def mapOutcome (N : EffectValuedMeasure Ω' E) (f : Ω' → Ω) (hf : Measurable f) :
    EffectValuedMeasure Ω E where
  toFun s hs := N (f ⁻¹' s) (hf hs)
  map_empty' := by simp
  map_univ' := by simp
  countably_additive' s hs hd := by
    simpa only [Set.preimage_iUnion] using N.countably_additive (fun n => hf (hs n))
      fun i j hij => Set.disjoint_left.2 fun x hxi hxj =>
        Set.disjoint_left.1 (hd hij) hxi hxj

@[simp]
lemma coe_mapOutcome_apply (N : EffectValuedMeasure Ω' E) (f : Ω' → Ω) (hf : Measurable f)
    (s : Set Ω) (hs : MeasurableSet s) : (N.mapOutcome f hf s hs : E) = N (f ⁻¹' s) (hf hs) :=
  rfl

end EffectValuedMeasure

end ProbabilisticTheory
