/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Particles.SuperSymmetry.SU5.ChargeSpectrum.Completions
/-!
# Minimal super set

## i. Overview

The minimally super set of a spectrum of charges `x` is the finite set of
spectrums of charges `y` such that `x ⊆ y` and there is no `z` such that `x ⊆ z ⊂ y`.
The minimal super set is defined using a finite set of possible charges in the `5`-bar and `10`
representations of `su(5)`. This is to ensure that the minimal super set is itself finite.

In this file we define the minimal super set and prove some basic properties of it.

## ii. Key results

- `minimalSuperSet`: the minimal super set of a charge spectrum.
- `exists_minimalSuperSet`: the existence of a member of the minimal super set
  between two charge spectra.
- `subset_insert_filter_card_zero`: a statement related to closure properties of multisets
  of charge spectra under a proposition `p` satisfying certain properties. The proof
  of this result relies on induction on minimal super sets.

## iii. Table of contents

- A. The minimal super set
  - A.1. Members of the minimal super set are super sets
  - A.2. Self is not a member of the minimal super set
  - A.3. Cardinality of member of the minimal super set
  - A.4. Inserting charges and minimal super sets
  - A.5. Existence of a minimal super set member between two charges
- B. Induction properties on the minimal super set
  - B.1. Lifting propositions from minimal super sets to super sets
  - B.2. Closure of multisets based on proposition for minimal super sets
  - B.3. Closure of multisets based on propositions

## iv. References

There are no known references for the material in this file.

-/

namespace SuperSymmetry

namespace SU5

namespace ChargeSpectrum

variable {𝓩 : Type} [DecidableEq 𝓩]

/-!

## A. The minimal super set

We define the minimal super set.

-/
/-- Given a collection of charges `x` in `ofFinset S5 S10`,
  the minimal charges `y` in `ofFinset S5 S10` which are a super sets of `x`. -/
def minimalSuperSet (S5 S10 : Finset 𝓩) (x : ChargeSpectrum 𝓩) : Finset (ChargeSpectrum 𝓩) :=
  let SqHd := if x.qHd.isSome then ∅ else S5.map ⟨fun y => ⟨some y, x.qHu, x.Q5, x.Q10⟩,
    by intro y1 y2; simp⟩
  let SqHu := if x.qHu.isSome then ∅ else S5.image fun y => ⟨x.qHd, some y, x.Q5, x.Q10⟩
  let SQ5 := (S5 \ x.Q5).image (fun y => ⟨x.qHd, x.qHu, insert y x.Q5, x.Q10⟩)
  let SQ10 := (S10 \ x.Q10).image (fun y => ⟨x.qHd, x.qHu, x.Q5, insert y x.Q10⟩)
  (SqHd ∪ SqHu ∪ SQ5 ∪ SQ10).erase x

/-!

### A.1. Members of the minimal super set are super sets

We show the basic property of a member `y ∈ minimalSuperSet S5 S10 x`, that is
that they are indeed super sets, namely `x ⊆ y`.

-/

lemma self_subset_mem_minimalSuperSet (S5 S10 : Finset 𝓩) (x y : ChargeSpectrum 𝓩)
    (hy : y ∈ minimalSuperSet S5 S10 x) : x ⊆ y := by
  simp [minimalSuperSet] at hy
  rcases hy with ⟨hy1, hr | hr | hr | hr⟩
  · match x with
    | ⟨none, _, _, _⟩ =>
      simp at hr
      obtain ⟨a, ha, rfl⟩ := hr
      rw [Subset]
      simp [hasSubset]
    | ⟨some x1, _, _, _⟩ =>
      simp at hr
  · match x with
    | ⟨_, none, _, _⟩ =>
      simp at hr
      obtain ⟨a, ha, rfl⟩ := hr
      rw [Subset]
      simp [hasSubset]
    | ⟨_, some x2, _, _⟩ =>
      simp at hr
  · match x with
    | ⟨_, _, Q5, _⟩ =>
      simp at hr
      obtain ⟨a, ha, rfl⟩ := hr
      rw [Subset]
      simp [hasSubset]
  · match x with
    | ⟨_, _, _, Q10⟩ =>
      simp at hr
      obtain ⟨a, ha, rfl⟩ := hr
      rw [Subset]
      simp [hasSubset]

/-!

### A.2. Self is not a member of the minimal super set

A charge spectrum is not a member of its own minimal super set. We give
two different forms of this result.

-/

@[simp]
lemma self_not_mem_minimalSuperSet (S5 S10 : Finset 𝓩) (x : ChargeSpectrum 𝓩) :
    x ∉ minimalSuperSet S5 S10 x := by
  simp [minimalSuperSet]

lemma self_ne_mem_minimalSuperSet (S5 S10 : Finset 𝓩) (x y : ChargeSpectrum 𝓩)
    (hy : y ∈ minimalSuperSet S5 S10 x) : x ≠ y := by
  by_contra h
  subst h
  simp at hy

/-!

### A.3. Cardinality of member of the minimal super set

We show that any member `y` of the minimal super set of `x` has cardinality one more than
that of `x`. I.e. it contains exactly one more unique charge.

-/

lemma card_of_mem_minimalSuperSet {S5 S10 : Finset 𝓩} {x : ChargeSpectrum 𝓩}
    (y : ChargeSpectrum 𝓩) (hy : y ∈ minimalSuperSet S5 S10 x) :
    card y = card x + 1 := by
  simp [minimalSuperSet] at hy
  rcases hy with ⟨hy1, hr | hr | hr | hr⟩
  · match x with
    | ⟨none, _, _, _⟩ =>
      simp at hr
      obtain ⟨a, ha, rfl⟩ := hr
      simp [card]
      omega
    | ⟨some x1, _, _, _⟩ =>
      simp at hr
  · match x with
    | ⟨_, none, _, _⟩ =>
      simp at hr
      obtain ⟨a, ha, rfl⟩ := hr
      simp [card]
      omega
    | ⟨_, some x2, _, _⟩ =>
      simp at hr
  · match x with
    | ⟨_, _, Q5, _⟩ =>
      simp at hr
      obtain ⟨a, ha, rfl⟩ := hr
      simp [card]
      rw [Finset.card_insert_of_notMem]
      omega
      by_contra h
      rw [Finset.insert_eq_of_mem h] at hy1
      simp at hy1
  · match x with
    | ⟨_, _, _, Q10⟩ =>
      simp at hr
      obtain ⟨a, ha, rfl⟩ := hr
      simp [card]
      rw [Finset.card_insert_of_notMem]
      omega
      by_contra h
      rw [Finset.insert_eq_of_mem h] at hy1
      simp at hy1

/-!

### A.4. Inserting charges and minimal super sets

We show that inserting a charge from `S5` or `S10` into `x`'s `Q5` or `Q10` respectively
which is not already present in `x` gives a member of the minimal super set.

Likewise we show that if `x` has no `qHd` or `qHu` charge, then inserting a charge from `S5`
into `qHd` or `qHu` respectively gives a member of the minimal super set.

-/

lemma insert_Q5_mem_minimalSuperSet {S5 S10 : Finset 𝓩} {x : ChargeSpectrum 𝓩}
    (z : 𝓩) (hz : z ∈ S5) (hznot : z ∉ x.Q5) :
    ⟨x.qHd, x.qHu, insert z x.Q5, x.Q10⟩ ∈ minimalSuperSet S5 S10 x := by
  simp [minimalSuperSet]
  match x with
  | ⟨qHd, qHu, Q5, Q10⟩ =>
  apply And.intro
  · simpa using hznot
  · right
    right
    left
    use z

lemma insert_Q10_mem_minimalSuperSet {S5 S10 : Finset 𝓩} {x : ChargeSpectrum 𝓩}
    (z : 𝓩) (hz : z ∈ S10) (hznot : z ∉ x.Q10) :
    ⟨x.qHd, x.qHu, x.Q5, insert z x.Q10⟩ ∈ minimalSuperSet S5 S10 x := by
  simp [minimalSuperSet]
  match x with
  | ⟨qHd, qHu, Q5, Q10⟩ =>
  apply And.intro
  · simpa using hznot
  · right
    right
    right
    use z

lemma some_qHd_mem_minimalSuperSet_of_none {S5 S10 : Finset 𝓩}
    {x2 : Option 𝓩 × Finset 𝓩 × Finset 𝓩} (z : 𝓩) (hz : z ∈ S5) :
    ⟨some z, x2.1, x2.2.1, x2.2.2⟩ ∈ minimalSuperSet S5 S10 ⟨none, x2.1, x2.2.1, x2.2.2⟩ := by
  simp_all [minimalSuperSet]

lemma some_qHu_mem_minimalSuperSet_of_none {S5 S10 : Finset 𝓩}
    {x1 : Option 𝓩} {x2 : Finset 𝓩 × Finset 𝓩} (z : 𝓩) (hz : z ∈ S5) :
    ⟨x1, some z, x2.1,x2.2⟩ ∈ minimalSuperSet S5 S10 ⟨x1, none, x2.1, x2.2⟩ := by
  simp_all [minimalSuperSet]

/-!

### A.5. Existence of a minimal super set member between two charges

We show that if `y` has charges from `S5` and `S10` and is a super set of `x` but not equal to `x`
then there is a `z` in the minimal super set of `x` which is a subset of `y`.

This shows, in a sense, that `minimalSuperSet` is "minimal", although it does not
go all the way to doing that. In particular, it does show that every minimal super set
is a member of `minimalSuperSet`.

-/

lemma exists_minimalSuperSet (S5 S10 : Finset 𝓩) {x y : ChargeSpectrum 𝓩}
    (hy : y ∈ ofFinset S5 S10) (hsubset : x ⊆ y)
    (hxneqy : x ≠ y) : ∃ z ∈ minimalSuperSet S5 S10 x, z ⊆ y := by
  rw [Subset] at hsubset
  dsimp [hasSubset] at hsubset
  match x, y with
  | ⟨x1, x2, x3, x4⟩, ⟨y1, y2, y3, y4⟩ =>
  simp at hxneqy
  by_cases h3 : x3 ≠ y3
  · have h3Strict : x3 ⊂ y3 := by
      refine Finset.ssubset_iff_subset_ne.mpr ?_
      simp_all
    rw [Finset.ssubset_iff_of_subset (by simp_all)] at h3Strict
    obtain ⟨z3, hz3, h3⟩ := h3Strict
    use ⟨x1, x2, insert z3 x3, x4⟩
    constructor
    · apply insert_Q5_mem_minimalSuperSet
      · simp [mem_ofFinset_iff] at hy
        apply hy.2.2.1 hz3
      · exact h3
    · rw [Subset]
      dsimp [hasSubset]
      simp_all
      rw [@Finset.insert_subset_iff]
      simp_all
  simp at h3
  subst h3
  by_cases h4 : x4 ≠ y4
  · have h4Strict : x4 ⊂ y4 := by
      refine Finset.ssubset_iff_subset_ne.mpr ?_
      simp_all
    rw [Finset.ssubset_iff_of_subset (by simp_all)] at h4Strict
    obtain ⟨z4, hz4, h4⟩ := h4Strict
    use ⟨x1, x2, x3, insert z4 x4⟩
    constructor
    · apply insert_Q10_mem_minimalSuperSet
      · simp [mem_ofFinset_iff] at hy
        apply hy.2.2.2 hz4
      · exact h4
    · rw [Subset]
      dsimp [hasSubset]
      simp_all
      rw [@Finset.insert_subset_iff]
      simp_all
  simp at h4
  subst h4
  simp_all
  match x1, y1, x2, y2 with
  | some x1, none, x2, y2 =>
    simp at hsubset
  | none, some y1, x2, y2 =>
    simp at hsubset
    use ⟨some y1, x2, x3, x4⟩
    constructor
    · have h0 := (some_qHd_mem_minimalSuperSet_of_none (S5 := S5) (S10 := S10) y1
        (by simp_all [mem_ofFinset_iff]) (x2 := (x2, x3, x4)))
      simpa using h0
    · simp_all [hasSubset]
  | x1, y1, some x2, none =>
    simp at hsubset
  | x1, y1, none, some y2 =>
    simp at hsubset
    use ⟨x1, some y2, x3, x4⟩
    constructor
    · have h0 := (some_qHu_mem_minimalSuperSet_of_none (x1 := x1) (S5 := S5) (S10 := S10) y2
        (by simp_all [mem_ofFinset_iff]) (x2 := (x3, x4)))
      simpa using h0
    · simp_all [hasSubset]
  | none, none, none, none =>
    simp_all
  | some x1, some y1, none, none =>
    simp_all
  | none, none, some x2, some y2 =>
    simp_all
  | some x1, some y1, some x2, some y2 =>
    simp_all

/-!

## B. Induction properties on the minimal super set

We now prove a number of induction properties related to minimal super sets.

-/

/-!

### B.1. Lifting propositions from minimal super sets to super sets

We show that for a proposition `p` on charge spectra with the property that
it is true on all minimal super sets of `x` if it true on `x` itself, then it is true on all
super sets of `x` if it is true for `x` itself.

-/

lemma minimalSuperSet_induction_on_inductive {S5 S10 : Finset 𝓩}
    (p : ChargeSpectrum 𝓩 → Prop)
    (hp : (x : ChargeSpectrum 𝓩) → p x → ∀ y ∈ minimalSuperSet S5 S10 x, p y)
    (x : ChargeSpectrum 𝓩) (hbase : p x)
    (y : ChargeSpectrum 𝓩) (hy : y ∈ ofFinset S5 S10) (hsubset : x ⊆ y) :
    (n : ℕ) → (hn : n = y.card - x.card) → p y
  | 0, hn => by
    have hxy : x = y := by
      refine eq_of_subset_card hsubset ?_
      have hl : card x ≤ card y := card_mono hsubset
      omega
    subst hxy
    simp_all
  | Nat.succ n, hn => by
    have hxy : x ≠ y := by
      intro h
      subst h
      simp at hn
    obtain ⟨z, hz, hsubsetz⟩ := exists_minimalSuperSet S5 S10 hy hsubset hxy
    refine minimalSuperSet_induction_on_inductive p hp z ?_ y hy ?_ n ?_
    · exact hp x hbase z hz
    · exact hsubsetz
    · rw [card_of_mem_minimalSuperSet z hz]
      omega

/-!

### B.2. Closure of multisets based on proposition for minimal super sets

We show that for a predicate `p` on charge spectrum,
if a multiset `T` of complete charge spectra has the property that
- all insertions of a `q10` charge either ends in `T` or fails `p`.
- all insertions of a `q5` charge either ends in `T` or fails `p`.
Then if `x` is in `T` then all members of the minimal super set of `x` either
are in `T` or fail `p`.

-/
variable {𝓩 : Type} [DecidableEq 𝓩]

lemma insert_filter_card_zero
    (T : Multiset (ChargeSpectrum 𝓩)) (S5 S10 : Finset 𝓩)
    (p : ChargeSpectrum 𝓩 → Prop) [DecidablePred p]
    (hComplet : ∀ x ∈ T, IsComplete x)
    (h10 : ∀ q10 : S10, ((T.map fun x => ⟨x.qHd, x.qHu, x.Q5, insert q10.1 x.Q10⟩).filter
      fun y => (y ∉ T ∧ p y)) = ∅)
    (h5 : ∀ q5 : S5, ((T.map fun x => ⟨x.qHd, x.qHu, insert q5.1 x.Q5, x.Q10⟩).filter
      fun y => (y ∉ T ∧ p y)) = ∅) :
    ∀ x ∈ T, ∀ y ∈ minimalSuperSet S5 S10 x, y ∉ T → ¬ p y := by
  intro ⟨xqHd, xqHu, xQ5, xQ10⟩ x_mem_T y y_mem_minimalSuperSet y_not_in_T
  have x_isComplete : IsComplete ⟨xqHd, xqHu, xQ5, xQ10⟩ := hComplet _ x_mem_T
  have xqHd_isSome : xqHd.isSome := by
    simp [IsComplete] at x_isComplete
    exact x_isComplete.1
  rw [Option.isSome_iff_exists] at xqHd_isSome
  obtain ⟨xqHd, rfl⟩ := xqHd_isSome
  have xqHu_isSome : xqHu.isSome := by
    simp [IsComplete] at x_isComplete
    exact x_isComplete.1
  rw [Option.isSome_iff_exists] at xqHu_isSome
  obtain ⟨xqHu, rfl⟩ := xqHu_isSome
  simp [minimalSuperSet] at y_mem_minimalSuperSet
  simp_all
  rcases y_mem_minimalSuperSet with ⟨q5, q5_mem_S5, rfl⟩ | ⟨q10, q10_mem_S10, rfl⟩
  · have h5' := h5 q5 q5_mem_S5.1
    exact h5' ⟨some xqHd, some xqHu, xQ5, xQ10⟩ x_mem_T y_not_in_T
  · have h10' := h10 q10 q10_mem_S10.1
    exact h10' ⟨some xqHd, some xqHu, xQ5, xQ10⟩ x_mem_T y_not_in_T

/-!

### B.3. Closure of multisets based on propositions

We show that for a predicate `p` on charge spectrum which if false on a charge spectrum
is also false on all its super sets,
if a multiset `T` of complete charge spectra has the property that
- all insertions of a `q10` charge either ends in `T` or fails `p`.
- all insertions of a `q5` charge either ends in `T` or fails `p`.
Then if `y` is not in `T` then it does not satisfy `p`.

We first prove this with an explicit induction argument, `n`, and then
we prove it in a more user friendly way.

-/

lemma subset_insert_filter_card_zero_inductive
    (T : Multiset (ChargeSpectrum 𝓩))
    (S5 S10 : Finset 𝓩)
    (p : ChargeSpectrum 𝓩 → Prop) [DecidablePred p]
    (hnotSubset : ∀ (x y : ChargeSpectrum 𝓩), x ⊆ y → ¬ p x → ¬ p y)
    (hComplet : ∀ x ∈ T, IsComplete x)
    (x : ChargeSpectrum 𝓩)
    (hx : x ∈ T) (y : ChargeSpectrum 𝓩) (hsubset : x ⊆ y)
    (hy : y ∈ ofFinset S5 S10)
    (h10 : ∀ q10 : S10, ((T.map fun x => ⟨x.qHd, x.qHu, x.Q5, insert q10.1 x.Q10⟩).filter
      fun y => (y ∉ T ∧ p y)) = ∅)
    (h5 : ∀ q5 : S5, ((T.map fun x => ⟨x.qHd, x.qHu, insert q5.1 x.Q5, x.Q10⟩).filter
      fun y => (y ∉ T ∧ p y)) = ∅) :
    (n : ℕ) → (hn : n = y.card - x.card) → y ∉ T → ¬ p y
  | 0, hn, hnot_in_T => by
    have hxy : x = y := by
      refine eq_of_subset_card hsubset ?_
      have hl : x.card ≤ y.card := card_mono hsubset
      omega
    subst hxy
    simp_all
  | Nat.succ n, hn, hnot_in_T => by
    have hxy : x ≠ y := by
      intro h
      subst h
      simp at hn
    obtain ⟨z, hz, hsubsetz⟩ := exists_minimalSuperSet S5 S10 hy hsubset hxy
    have hz' := insert_filter_card_zero T S5 S10 p hComplet h10 h5 x hx z hz
    by_cases hz_not_in_T : z ∉ T
    · apply hnotSubset
      · exact hsubsetz
      · exact hz' hz_not_in_T
    apply subset_insert_filter_card_zero_inductive T S5 S10 p hnotSubset hComplet z (n := n)
    · simpa using hz_not_in_T
    · exact hsubsetz
    · exact hy
    · exact fun q10 => h10 q10
    · exact fun q5 => h5 q5
    · rw [card_of_mem_minimalSuperSet z hz]
      omega
    · exact hnot_in_T

/-- For a proposition `p` if `(T.uniqueMap4 (insert q10.1)).toMultiset.filter p`
  and `(T.uniqueMap3 (insert q5.1)).toMultiset.filter p` for all `q5 ∈ S5` and `q10 ∈ S10` then
  if `x ∈ T` and `x ⊆ y` if `y ∉ T` then `¬ p y`.
  This assumes that all charges in `T` are complete, and that `p` satisfies
  `x ⊆ y → ¬ p x → ¬ p y`. -/
lemma subset_insert_filter_card_zero
    (T : Multiset (ChargeSpectrum 𝓩))
    (S5 S10 : Finset 𝓩)
    (p : ChargeSpectrum 𝓩 → Prop) [DecidablePred p]
    (hnotSubset : ∀ (x y : ChargeSpectrum 𝓩), x ⊆ y → ¬ p x → ¬ p y)
    (hComplet : ∀ x ∈ T, IsComplete x)
    (x : ChargeSpectrum 𝓩)
    (hx : x ∈ T) (y : ChargeSpectrum 𝓩) (hsubset : x ⊆ y)
    (hy : y ∈ ofFinset S5 S10)
    (h10 : ∀ q10 : S10, ((T.map fun x => ⟨x.qHd, x.qHu, x.Q5, insert q10.1 x.Q10⟩).filter
      fun y => (y ∉ T ∧ p y)) = ∅)
    (h5 : ∀ q5 : S5, ((T.map fun x => ⟨x.qHd, x.qHu, insert q5.1 x.Q5, x.Q10⟩).filter
      fun y => (y ∉ T ∧ p y)) = ∅) :
      y ∉ T → ¬ p y :=
  subset_insert_filter_card_zero_inductive T S5 S10 p hnotSubset hComplet x hx y hsubset hy h10 h5
    (y.card - x.card) rfl

end ChargeSpectrum

end SU5

end SuperSymmetry
