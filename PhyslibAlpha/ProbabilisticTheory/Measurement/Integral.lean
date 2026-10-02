/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.Measurement.EffectValuedMeasure

/-!

# Integrating simple functions against an effect-valued measure

## i. Overview

An effect-valued measure `μ` assigns an effect to every event. Integrating a simple function `∑ᵢ cᵢ
𝟙_{sᵢ}` against it gives `∑ᵢ cᵢ μ(sᵢ)`. The effect-valued measure is finitely additive, so this does
not depend on how the function is written: two partitions representing the same function give the
same value, by passing to their common refinement. The integral is linear and positive.

## ii. Key results

- `EffectValuedMeasure.apply_iUnion_of_disjoint` : finite additivity.
- `EffectValuedMeasure.IsPartition` : finite measurable partitions.
- `EffectValuedMeasure.simpleIntegral` : the integral `∑ᵢ cᵢ μ(sᵢ)` of a simple function.
- `EffectValuedMeasure.simpleIntegral_eq_of_pointwise_eq` : the integral depends only on the
  function.
- `EffectValuedMeasure.simpleIntegral_nonneg` : the integral is positive.

## iii. Table of contents

- A. Finite measurable partitions and simple functions
- B. Finite additivity
- C. The integral of a simple function

-/

@[expose] public section

namespace ProbabilisticTheory

namespace EffectValuedMeasure

/-! ## A. Finite measurable partitions and simple functions

Nothing here refers to `E` or to a POVM at all yet: a partition and the simple function it carries
are facts about `Ω` alone. -/

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `s` is a finite measurable partition of `Ω`: its pieces are measurable, pairwise disjoint, and
cover `Ω`. This is the "unbundled `he : ∑ i, e i = 1`" of `Measurement.toChannel`
transported to the measure-theoretic setting: there, a finite family of
effects summing to the certain event; here, a finite family of sets whose indicators sum to the
constant function `1`. -/
structure IsPartition {ι : Type*} [Fintype ι] (s : ι → Set Ω) : Prop where
  /-- Every piece of the partition is measurable. -/
  measurable : ∀ i, MeasurableSet (s i)
  /-- Distinct pieces of the partition are disjoint. -/
  disjoint : ∀ i j, i ≠ j → Disjoint (s i) (s j)
  /-- The pieces cover all of `Ω`. -/
  cover : ⋃ i, s i = Set.univ

/-- The simple function `∑ᵢ cᵢ 𝟙_{sᵢ}` of a partition. -/
noncomputable def simpleValue {ι : Type*} [Fintype ι] (c : ι → ℝ) (s : ι → Set Ω) (x : Ω) : ℝ :=
  ∑ i, (s i).indicator (fun _ => c i) x

/-- At a point lying in piece `i` of the partition, the simple function evaluates to `c i`: every
other term of the defining sum vanishes since the pieces are pairwise disjoint. -/
lemma simpleValue_apply_of_mem {ι : Type*} [Fintype ι] {c : ι → ℝ} {s : ι → Set Ω}
    (hs : IsPartition s) {x : Ω} {i : ι} (hx : x ∈ s i) : simpleValue c s x = c i := by
  unfold simpleValue
  rw [Finset.sum_eq_single i (fun j _ hji => Set.indicator_of_notMem
      (fun hxj => absurd hx (Set.disjoint_left.mp (hs.disjoint j i hji) hxj)) _)
    (fun h => absurd (Finset.mem_univ i) h)]
  exact Set.indicator_of_mem hx _

end EffectValuedMeasure

variable {Ω E : Type*} [MeasurableSpace Ω] [OrderUnitSpace E]

namespace EffectValuedMeasure

/-! ## B. Finite additivity

`EffectValuedMeasure` only bundles *countable* additivity (`countably_additive`). Finite
additivity is the special case of a family that is eventually `∅`, and the least upper bound of an
eventually-constant, nondecreasing sequence (nondecreasing since every value of `μ` is a
nonnegative effect) is just its eventual value — which is what lets us read finite sums off
`countably_additive` directly. -/

/-- Applying `μ` only depends on the set, not on which proof of measurability is supplied — an
immediate consequence of `Set` equality and proof irrelevance, recorded here since it comes up
whenever a set is simplified (e.g. `if`-reduced) mid-computation. -/
lemma apply_congr (μ : EffectValuedMeasure Ω E) {s t : Set Ω} (h : s = t)
    {hs : MeasurableSet s} {ht : MeasurableSet t} : (μ s hs : E) = (μ t ht : E) := by
  subst h; rfl

/-- Padding a finite disjoint family with `∅` and applying countable additivity: past the point
where every remaining piece is `∅`, the partial sums have stabilized, and since they are also
nondecreasing (every value of `μ` is a nonnegative effect), that stable value is already the least
upper bound `countably_additive` promises — so it computes `μ` of the union. -/
lemma apply_iUnion_eq_sum_of_eventually_empty (μ : EffectValuedMeasure Ω E) (t : ℕ → Set Ω)
    (htm : ∀ n, MeasurableSet (t n)) (htd : ∀ m n, m ≠ n → Disjoint (t m) (t n)) {N : ℕ}
    (hN : ∀ n, N ≤ n → t n = ∅) :
    (μ (⋃ n, t n) (MeasurableSet.iUnion htm) : E) =
      ∑ n ∈ Finset.range N, (μ (t n) (htm n) : E) := by
  set g : ℕ → E := fun n => (μ (t n) (htm n) : E) with hg_def
  have hg0 : ∀ n, 0 ≤ g n := fun n => (μ (t n) (htm n)).2.1
  have hgN : ∀ n, N ≤ n → g n = 0 := fun n hn => by
    show (μ (t n) (htm n) : E) = 0
    rw [apply_congr μ (hN n hn) (ht := MeasurableSet.empty)]
    simp
  have hPmono : Monotone (fun M => ∑ n ∈ Finset.range M, g n) := by
    apply monotone_nat_of_le_succ
    intro n
    rw [Finset.sum_range_succ]
    exact le_add_of_nonneg_right (hg0 n)
  have hPstable : ∀ M, N ≤ M → (∑ n ∈ Finset.range M, g n) = ∑ n ∈ Finset.range N, g n := by
    intro M hM
    induction M, hM using Nat.le_induction with
    | base => rfl
    | succ M hM ih => rw [Finset.sum_range_succ, ih, hgN M hM, add_zero]
  have hgreatest : IsGreatest (Set.range (fun M => ∑ n ∈ Finset.range M, g n))
      (∑ n ∈ Finset.range N, g n) := by
    refine ⟨⟨N, rfl⟩, ?_⟩
    rintro _ ⟨M, rfl⟩
    rcases le_total M N with hMN | hMN
    · exact hPmono hMN
    · exact (hPstable M hMN).le
  have hlub1 : IsLUB (Set.range (fun M => ∑ n ∈ Finset.range M, g n))
      (∑ n ∈ Finset.range N, g n) := hgreatest.isLUB
  have hlub2 : IsLUB (Set.range (fun M => ∑ n ∈ Finset.range M, g n))
      (μ (⋃ n, t n) (MeasurableSet.iUnion htm) : E) := μ.countably_additive htm htd
  exact IsLUB.unique hlub2 hlub1

/-- Binary additivity of `μ`, derived from countable additivity by padding a two-element family
with `∅`. -/
lemma apply_union_of_disjoint (μ : EffectValuedMeasure Ω E) {A B : Set Ω}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : Disjoint A B) :
    (μ (A ∪ B) (hA.union hB) : E) = (μ A hA : E) + (μ B hB : E) := by
  classical
  set t : ℕ → Set Ω := fun n => if n = 0 then A else if n = 1 then B else ∅ with ht_def
  have htm : ∀ n, MeasurableSet (t n) := fun n => by
    rw [ht_def]
    show MeasurableSet (if n = 0 then A else if n = 1 then B else ∅)
    split_ifs with h0 h1
    exacts [hA, hB, MeasurableSet.empty]
  have htd : ∀ m n, m ≠ n → Disjoint (t m) (t n) := by
    intro m n hmn
    rw [ht_def]
    show Disjoint (if m = 0 then A else if m = 1 then B else ∅)
      (if n = 0 then A else if n = 1 then B else ∅)
    split_ifs with hm0 hn0 hn0 hm1 hn1 hn1
    · exact absurd (hm0.trans hn0.symm) hmn
    · exact hAB
    · exact Set.disjoint_empty A
    · exact hAB.symm
    · exact absurd (hm1.trans hn1.symm) hmn
    · exact Set.disjoint_empty B
    · exact Set.empty_disjoint A
    · exact Set.empty_disjoint B
    · exact Set.disjoint_empty ∅
  have hUn : (⋃ n, t n) = A ∪ B := by
    ext x
    simp only [Set.mem_iUnion, ht_def]
    constructor
    · rintro ⟨n, hn⟩
      split_ifs at hn with h0 h1
      · exact Or.inl hn
      · exact Or.inr hn
      · exact absurd hn (Set.notMem_empty x)
    · rintro (hx | hx)
      · exact ⟨0, by simp [hx]⟩
      · exact ⟨1, by simp [hx]⟩
  have hN : ∀ n, 2 ≤ n → t n = ∅ := fun n hn => by
    rw [ht_def]
    show (if n = 0 then A else if n = 1 then B else ∅) = ∅
    have h0 : n ≠ 0 := by omega
    have h1 : n ≠ 1 := by omega
    simp [h0, h1]
  have key := apply_iUnion_eq_sum_of_eventually_empty μ t htm htd (N := 2) hN
  rw [apply_congr μ hUn (ht := hA.union hB)] at key
  rw [key, Finset.sum_range_succ, Finset.sum_range_one]
  refine congrArg₂ (· + ·) (apply_congr μ ?_) (apply_congr μ ?_)
  · rw [ht_def]; simp
  · rw [ht_def]; simp

/-- Finite additivity of `μ` over a pairwise disjoint family indexed by a `Finset`, with the
disjointness only required on the labels actually occurring in `s`. Proved by induction on the
`Finset`, peeling one element off at a time using binary additivity
(`apply_union_of_disjoint`). -/
lemma apply_biUnion_of_disjoint {ι : Type*} [DecidableEq ι] (μ : EffectValuedMeasure Ω E)
    (f : ι → Set Ω) (hfm : ∀ i, MeasurableSet (f i)) (s : Finset ι)
    (hfd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (f i) (f j)) :
    (μ (⋃ i ∈ s, f i) (s.measurableSet_biUnion fun i _ => hfm i) : E) =
      ∑ i ∈ s, (μ (f i) (hfm i) : E) := by
  induction s using Finset.induction with
  | empty =>
    refine (apply_congr μ ?_ (ht := MeasurableSet.empty)).trans ?_
    · simp
    · simp [μ.map_empty]
  | insert a s ha ih =>
    have hfd' : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (f i) (f j) := fun i hi j hj =>
      hfd i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj)
    have hdisj : Disjoint (f a) (⋃ i ∈ s, f i) := by
      rw [Set.disjoint_iUnion_right]
      intro i
      rw [Set.disjoint_iUnion_right]
      intro hi
      exact hfd a (Finset.mem_insert_self a s) i (Finset.mem_insert_of_mem hi)
        (ne_of_mem_of_not_mem hi ha).symm
    have hUn : (⋃ i ∈ insert a s, f i) = f a ∪ ⋃ i ∈ s, f i := by
      ext x
      simp only [Set.mem_iUnion, Finset.mem_insert, Set.mem_union]
      constructor
      · rintro ⟨i, hi | hi, hx⟩
        · exact Or.inl (hi ▸ hx)
        · exact Or.inr ⟨i, hi, hx⟩
      · rintro (hx | ⟨i, hi, hx⟩)
        · exact ⟨a, Or.inl rfl, hx⟩
        · exact ⟨i, Or.inr hi, hx⟩
    have step :=
      apply_union_of_disjoint μ (hfm a) (s.measurableSet_biUnion fun i _ => hfm i) hdisj
    rw [apply_congr μ hUn
      (ht := (hfm a).union (s.measurableSet_biUnion fun i _ => hfm i))]
    rw [step, ih hfd', Finset.sum_insert ha]

/-- Finite additivity of `μ` over a `Fintype`-indexed pairwise disjoint family: the workhorse used
throughout the rest of this file. -/
lemma apply_iUnion_of_disjoint {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : EffectValuedMeasure Ω E) (f : ι → Set Ω) (hfm : ∀ i, MeasurableSet (f i))
    (hfd : ∀ i j, i ≠ j → Disjoint (f i) (f j)) :
    (μ (⋃ i, f i) (MeasurableSet.iUnion hfm) : E) = ∑ i, (μ (f i) (hfm i) : E) := by
  have h := apply_biUnion_of_disjoint μ f hfm Finset.univ (fun i _ j _ hij => hfd i j hij)
  rw [apply_congr μ (t := ⋃ i, f i) (by simp) (ht := MeasurableSet.iUnion hfm)] at h
  simpa using h

/-! ## C. The integral of a simple function -/

/-- The integral of the simple function `∑ i, c i • 𝟙_{s i}` against `μ`: `∑ i, c i • μ(s i)`.
Well-defined independently of the chosen partition by `simpleIntegral_eq_of_pointwise_eq`, and
this is exactly `Measurement.toChannel` in the case where every piece of
the partition is a single point mass. -/
noncomputable def simpleIntegral {ι : Type*} [Fintype ι] (μ : EffectValuedMeasure Ω E)
    (c : ι → ℝ) (s : ι → Set Ω) (hs : IsPartition s) : E :=
  ∑ i, c i • (μ (s i) (hs.measurable i) : E)

/-- On a partition, the piece `s i` decomposes as the union of its intersections with every piece
of a second partition `s'`: `s'` covers `Ω`, so intersecting with `s i` covers `s i`. Used to
refine two partitions to their common refinement in `simpleIntegral_eq_of_pointwise_eq`. -/
lemma apply_eq_sum_inter {ι ι' : Type*} [Fintype ι] [Fintype ι'] [DecidableEq ι']
    (μ : EffectValuedMeasure Ω E) {s : ι → Set Ω} {s' : ι' → Set Ω} (hs : IsPartition s)
    (hs' : IsPartition s') (i : ι) :
    (μ (s i) (hs.measurable i) : E) =
      ∑ j, (μ (s i ∩ s' j) ((hs.measurable i).inter (hs'.measurable j)) : E) := by
  have hi_eq : s i = ⋃ j, s i ∩ s' j := by
    rw [← Set.inter_iUnion, hs'.cover, Set.inter_univ]
  rw [apply_congr μ hi_eq
    (ht := MeasurableSet.iUnion fun j => (hs.measurable i).inter (hs'.measurable j))]
  exact apply_iUnion_of_disjoint μ (fun j => s i ∩ s' j)
    (fun j => (hs.measurable i).inter (hs'.measurable j))
    (fun j k hjk => Disjoint.mono Set.inter_subset_right Set.inter_subset_right
      (hs'.disjoint j k hjk))

/-- The symmetric counterpart of `apply_eq_sum_inter`, with the roles of the two partitions
swapped: the piece `s' j` decomposes as the union of its intersections with every piece of `s`. -/
lemma apply_eq_sum_inter' {ι ι' : Type*} [Fintype ι] [Fintype ι'] [DecidableEq ι]
    (μ : EffectValuedMeasure Ω E) {s : ι → Set Ω} {s' : ι' → Set Ω} (hs : IsPartition s)
    (hs' : IsPartition s') (j : ι') :
    (μ (s' j) (hs'.measurable j) : E) =
      ∑ i, (μ (s i ∩ s' j) ((hs.measurable i).inter (hs'.measurable j)) : E) := by
  rw [apply_eq_sum_inter μ hs' hs j]
  exact Finset.sum_congr rfl fun i _ => apply_congr μ (Set.inter_comm (s' j) (s i))

/-- **The simple integral depends only on the function.** Two partitions describing the same
function give the same integral, by passing to the common refinement. -/
lemma simpleIntegral_eq_of_pointwise_eq {ι ι' : Type*} [Fintype ι] [Fintype ι'] [DecidableEq ι]
    [DecidableEq ι'] (μ : EffectValuedMeasure Ω E) (c : ι → ℝ) (s : ι → Set Ω) (hs : IsPartition s)
    (c' : ι' → ℝ)
    (s' : ι' → Set Ω) (hs' : IsPartition s')
    (hval : ∀ x, simpleValue c s x = simpleValue c' s' x) :
    simpleIntegral μ c s hs = simpleIntegral μ c' s' hs' := by
  have hterm : ∀ i j, c i • (μ (s i ∩ s' j) ((hs.measurable i).inter (hs'.measurable j)) : E) =
      c' j • (μ (s i ∩ s' j) ((hs.measurable i).inter (hs'.measurable j)) : E) := by
    intro i j
    rcases Set.eq_empty_or_nonempty (s i ∩ s' j) with hempty | ⟨x, hx⟩
    · rw [apply_congr μ hempty (ht := MeasurableSet.empty)]
      simp
    · have hci : c i = simpleValue c s x := (simpleValue_apply_of_mem hs hx.1).symm
      have hcj : c' j = simpleValue c' s' x := (simpleValue_apply_of_mem hs' hx.2).symm
      rw [hci, hcj, hval x]
  have hlhs : simpleIntegral μ c s hs =
      ∑ i, ∑ j, c i • (μ (s i ∩ s' j) ((hs.measurable i).inter (hs'.measurable j)) : E) := by
    unfold simpleIntegral
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [apply_eq_sum_inter μ hs hs' i, Finset.smul_sum]
  have hrhs : simpleIntegral μ c' s' hs' =
      ∑ i, ∑ j, c' j • (μ (s i ∩ s' j) ((hs.measurable i).inter (hs'.measurable j)) : E) := by
    unfold simpleIntegral
    have step : ∑ j, c' j • (μ (s' j) (hs'.measurable j) : E) =
        ∑ j, ∑ i, c' j • (μ (s i ∩ s' j) ((hs.measurable i).inter (hs'.measurable j)) : E) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [apply_eq_sum_inter' μ hs hs' j, Finset.smul_sum]
    rw [step, Finset.sum_comm]
  rw [hlhs, hrhs]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hterm i j

variable {ι : Type*} [Fintype ι]

/-- The simple integral is additive in the weights, over a fixed partition. -/
lemma simpleIntegral_add (μ : EffectValuedMeasure Ω E) (c₁ c₂ : ι → ℝ) (s : ι → Set Ω)
    (hs : IsPartition s) :
    simpleIntegral μ (c₁ + c₂) s hs = simpleIntegral μ c₁ s hs + simpleIntegral μ c₂ s hs := by
  unfold simpleIntegral
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by rw [Pi.add_apply, add_smul]

/-- The simple integral is homogeneous in the weights, over a fixed partition. -/
lemma simpleIntegral_smul (μ : EffectValuedMeasure Ω E) (r : ℝ) (c : ι → ℝ) (s : ι → Set Ω)
    (hs : IsPartition s) :
    simpleIntegral μ (r • c) s hs = r • simpleIntegral μ c s hs := by
  unfold simpleIntegral
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [Pi.smul_apply, smul_eq_mul, mul_smul]

/-- The simple integral of a nonnegative simple function is nonnegative — matching `μ`'s own
positivity: every term `c i • μ(s i)` is a nonnegative scalar times a nonnegative effect. -/
lemma simpleIntegral_nonneg (μ : EffectValuedMeasure Ω E) {c : ι → ℝ} (hc : ∀ i, 0 ≤ c i)
    (s : ι → Set Ω) (hs : IsPartition s) : 0 ≤ simpleIntegral μ c s hs :=
  Finset.sum_nonneg fun i _ => smul_nonneg (hc i) (μ (s i) (hs.measurable i)).2.1

end EffectValuedMeasure

end ProbabilisticTheory
