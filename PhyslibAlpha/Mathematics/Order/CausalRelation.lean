/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Tactic.Bound.Init
public import Mathlib.Topology.Compactness.Compact

/-!

# Causal support geometry

## i. Overview

Causal futures and pasts describe the allowed support of linear field responses.

## ii. Key results

- `reverse` : Reversing the causal direction exchanges retarded and advanced support.
- `reverse` : Reversing the causal direction exchanges retarded and advanced support.
- `causalFuture` : The events reachable from at least one event of a source set.
- `causalPast` : The events able to influence at least one event of a target set.
- `causalHull` : The union of the causal past and future of a set.
- `IsSpacelikeCompact` : A closed field support is spacelike compact when it lies in the causal hull
  of a compact set.
- `HasCompactCausalDiamonds` : Compact causal diamonds are the geometric compactness input for Green
  exactness.
- `causalFuture` : The events reachable from at least one event of a source set.

## iii. Table of contents

- A. Causal support geometry
- B. Past-compact and future-compact support

## iv. References

None.

## A. Causal support geometry

- `reverse` : Reversing the causal direction exchanges retarded and advanced support.
- `reverse` : Reversing the causal direction exchanges retarded and advanced support.
- `causalFuture` : The events reachable from at least one event of a source set.
- `causalPast` : The events able to influence at least one event of a target set.
- `causalHull` : The union of the causal past and future of a set.
- `IsSpacelikeCompact` : A closed field support is spacelike compact when it lies in the causal hull
  of a compact set.
- `HasCompactCausalDiamonds` : Compact causal diamonds are the geometric compactness input for Green
  exactness.

Lemmas: `subset_causalFuture`, `subset_causalPast`, `causalFuture_mono`, `causalPast_mono`,
`causalHull_mono`, `causalFuture_empty`, `causalPast_empty`, `causalFuture_union`,
`causalPast_union`, `causalFuture_idem` and more.

## B. Past-compact and future-compact support

- `causalFuture` : The events reachable from at least one event of a source set.
- `IsPastCompact` : A set is past compact when its intersection with the causal past of every
  compact set is compact.

Lemmas: `mono`, `isPastCompact_empty`, `union`, `causalFuture_inter_causalPast`,
`isPastCompact_of_futureSupported`, `isClosed_causalFuture`.

-/

@[expose] public section

noncomputable section

open scoped Topology

/-- The causal relation used to bound field propagation. Further geometric hypotheses belong
in the results requiring them rather than in this minimal structure. -/
structure CausalRelation (M : Type*) where
  /-- An event can influence a causally later event. -/
  Precedes : M → M → Prop
  /-- Every event lies in its own causal future. -/
  refl : ∀ p, Precedes p p
  /-- Successive causal propagation is causal. -/
  trans : ∀ {p q r}, Precedes p q → Precedes q r → Precedes p r

namespace CausalRelation

section
variable {M : Type*} (C : CausalRelation M) {A B : Set M}

/-- Reversing the causal direction exchanges retarded and advanced support. -/
def reverse : CausalRelation M where
  Precedes p q := C.Precedes q p
  refl := C.refl
  trans hpq hqr := C.trans hqr hpq

/-- The events reachable from at least one event of a source set. -/
def causalFuture (A : Set M) : Set M := {q | ∃ p ∈ A, C.Precedes p q}

/-- The events able to influence at least one event of a target set. -/
def causalPast (A : Set M) : Set M := {p | ∃ q ∈ A, C.Precedes p q}

/-- The union of the causal past and future of a set. -/
def causalHull (A : Set M) : Set M := C.causalFuture A ∪ C.causalPast A

lemma subset_causalFuture : A ⊆ C.causalFuture A :=
  fun p hp => ⟨p, hp, C.refl p⟩

lemma subset_causalPast : A ⊆ C.causalPast A :=
  fun p hp => ⟨p, hp, C.refl p⟩

lemma causalFuture_mono (h : A ⊆ B) : C.causalFuture A ⊆ C.causalFuture B :=
  fun _ ⟨p, hp, hpq⟩ => ⟨p, h hp, hpq⟩

lemma causalPast_mono (h : A ⊆ B) : C.causalPast A ⊆ C.causalPast B :=
  fun _ ⟨q, hq, hpq⟩ => ⟨q, h hq, hpq⟩

lemma causalHull_mono (h : A ⊆ B) : C.causalHull A ⊆ C.causalHull B :=
  Set.union_subset_union (C.causalFuture_mono h) (C.causalPast_mono h)

@[simp]
lemma causalFuture_empty : C.causalFuture ∅ = ∅ := by
  ext p
  simp [causalFuture]

@[simp]
lemma causalPast_empty : C.causalPast ∅ = ∅ := by
  ext p
  simp [causalPast]

@[simp]
lemma causalFuture_union : C.causalFuture (A ∪ B) = C.causalFuture A ∪ C.causalFuture B := by
  ext p
  simp only [causalFuture, Set.mem_ofPred_eq, Set.mem_union]
  constructor
  · rintro ⟨q, hq | hq, hqp⟩
    · exact Or.inl ⟨q, hq, hqp⟩
    · exact Or.inr ⟨q, hq, hqp⟩
  · rintro (⟨q, hq, hqp⟩ | ⟨q, hq, hqp⟩)
    · exact ⟨q, Or.inl hq, hqp⟩
    · exact ⟨q, Or.inr hq, hqp⟩

@[simp]
lemma causalPast_union : C.causalPast (A ∪ B) = C.causalPast A ∪ C.causalPast B := by
  ext p
  simp only [causalPast, Set.mem_ofPred_eq, Set.mem_union]
  constructor
  · rintro ⟨q, hq | hq, hpq⟩
    · exact Or.inl ⟨q, hq, hpq⟩
    · exact Or.inr ⟨q, hq, hpq⟩
  · rintro (⟨q, hq, hpq⟩ | ⟨q, hq, hpq⟩)
    · exact ⟨q, Or.inl hq, hpq⟩
    · exact ⟨q, Or.inr hq, hpq⟩

@[simp]
lemma causalFuture_idem : C.causalFuture (C.causalFuture A) = C.causalFuture A := by
  apply Set.Subset.antisymm
  · rintro p ⟨q, ⟨r, hr, hrq⟩, hqp⟩
    exact ⟨r, hr, C.trans hrq hqp⟩
  · exact C.subset_causalFuture

@[simp]
lemma causalPast_idem : C.causalPast (C.causalPast A) = C.causalPast A := by
  apply Set.Subset.antisymm
  · rintro p ⟨q, ⟨r, hr, hqr⟩, hpq⟩
    exact ⟨r, hr, C.trans hpq hqr⟩
  · exact C.subset_causalPast

/-- A closed field support is spacelike compact when it lies in the causal hull of a compact set.
No equivalence with a Cauchy-surface definition is asserted without geometric hypotheses. -/
def IsSpacelikeCompact [TopologicalSpace M] (A : Set M) : Prop :=
  ∃ K : Set M, IsCompact K ∧ A ⊆ C.causalHull K

lemma IsSpacelikeCompact.mono [TopologicalSpace M]
    (hB : C.IsSpacelikeCompact B) (h : A ⊆ B) : C.IsSpacelikeCompact A := by
  obtain ⟨K, hK, hBK⟩ := hB
  exact ⟨K, hK, h.trans hBK⟩

/-- Compact causal diamonds are the geometric compactness input for Green exactness.
This does not by itself assert every part of global hyperbolicity. -/
def HasCompactCausalDiamonds [TopologicalSpace M] : Prop :=
  ∀ K L : Set M, IsCompact K → IsCompact L →
    IsCompact (C.causalFuture K ∩ C.causalPast L)

/-- Compact causal diamonds are unchanged by reversing time orientation. -/
lemma HasCompactCausalDiamonds.reverse [TopologicalSpace M]
    (h : C.HasCompactCausalDiamonds) : C.reverse.HasCompactCausalDiamonds := by
  intro K L hK hL
  change IsCompact (C.causalPast K ∩ C.causalFuture L)
  rw [Set.inter_comm]
  exact h L K hL hK
end

section
variable {M : Type*} [TopologicalSpace M] (C : CausalRelation M) {A B : Set M}

/-- A set is past compact when its intersection with the causal past of every compact set is
compact. -/
def IsPastCompact (A : Set M) : Prop :=
  ∀ K : Set M, IsCompact K → IsCompact (A ∩ C.causalPast K)

lemma isPastCompact_empty : C.IsPastCompact ∅ := by
  intro K _
  simp

lemma IsPastCompact.union (hA : C.IsPastCompact A) (hB : C.IsPastCompact B) :
    C.IsPastCompact (A ∪ B) := by
  intro K hK
  rw [Set.union_inter_distrib_right]
  exact (hA K hK).union (hB K hK)

/-- A closed subset of a past-compact set remains past compact. -/
lemma IsPastCompact.mono (hB : C.IsPastCompact B) (hA : IsClosed A) (hAB : A ⊆ B) :
    C.IsPastCompact A := by
  intro K hK
  have heq : A ∩ C.causalPast K = A ∩ (B ∩ C.causalPast K) := by
    ext x
    constructor
    · exact fun h => ⟨h.1, hAB h.1, h.2⟩
    · exact fun h => ⟨h.1, h.2.2⟩
  rw [heq]
  exact (hB K hK).inter_left hA

omit [TopologicalSpace M] in
/-- Causal transitivity localizes a future inside the past of an observation set. -/
lemma causalFuture_inter_causalPast (A K : Set M) :
    C.causalFuture A ∩ C.causalPast K =
      C.causalFuture (A ∩ C.causalPast K) ∩ C.causalPast K := by
  ext x
  constructor
  · rintro ⟨⟨a, ha, hax⟩, ⟨k, hk, hxk⟩⟩
    exact ⟨⟨a, ⟨ha, k, hk, C.trans hax hxk⟩, hax⟩, k, hk, hxk⟩
  · rintro ⟨⟨a, ha, hax⟩, hx⟩
    exact ⟨⟨a, ha.1, hax⟩, hx⟩

/-- Compact causal diamonds imply that the future of a past-compact source is past compact. -/
lemma IsPastCompact.causalFuture (hC : C.HasCompactCausalDiamonds) (hA : C.IsPastCompact A) :
    C.IsPastCompact (C.causalFuture A) := by
  intro K hK
  rw [C.causalFuture_inter_causalPast]
  exact hC _ K (hA K hK) hK

/-- Closed support in the future of a compact set is past compact under compact-diamond geometry. -/
lemma isPastCompact_of_futureSupported (hC : C.HasCompactCausalDiamonds)
    (hA : IsClosed A) {K : Set M} (hK : IsCompact K) (hAK : A ⊆ C.causalFuture K) :
    C.IsPastCompact A :=
  IsPastCompact.mono C (fun L hL => hC K L hK hL) hA hAK

/-- Local upper causal bounds and closed compact futures imply closed futures of past-compact sets.
These are geometric hypotheses, independent of the field equation or Green operators. -/
lemma IsPastCompact.isClosed_causalFuture
    (hclosed : ∀ K : Set M, IsCompact K → IsClosed (C.causalFuture K))
    (hlocal : ∀ p : M, ∃ K : Set M, IsCompact K ∧ C.causalPast K ∈ 𝓝 p)
    (hA : C.IsPastCompact A) : IsClosed (C.causalFuture A) := by
  apply isOpen_compl_iff.mp
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  obtain ⟨K, hK, hKp⟩ := hlocal p
  have hB := hclosed (A ∩ C.causalPast K) (hA K hK)
  have hpB : p ∉ C.causalFuture (A ∩ C.causalPast K) :=
    fun h => hp (C.causalFuture_mono Set.inter_subset_left h)
  filter_upwards [hKp, hB.isOpen_compl.mem_nhds hpB] with q hq hqB
  intro hqA
  have hq' : q ∈ C.causalFuture A ∩ C.causalPast K := ⟨hqA, hq⟩
  rw [C.causalFuture_inter_causalPast] at hq'
  exact hqB hq'.1
end

end CausalRelation
