/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Particles.SuperSymmetry.SU5.ChargeSpectrum.MinimallyAllowsTerm.Basic
import PhysLean.Particles.SuperSymmetry.SU5.ChargeSpectrum.PhenoConstrained
/-!

# The set of charges which minimally allows a potential term

## i. Overview

In this module given finite sets for the `5`-bar and `10`d charges `S5` and `S10`
we find the sets of charge spectra which minimally allowed a potential term `T`.
The set we will actually define will be a multiset, for computational
efficiency (using multisets saves Lean having to manually check for duplicates,
which can be very costly)

To do this we define some auxiliary results which create multisets of a given cardinality
from a finset.

## ii. Key results

- `minimallyAllowsTermsOfFinset S5 S10 T` : the multiset of all charge spectra
  with charges in `S5` and `S10` which minimally allow the potential term `T`.
- `minimallyAllowsTerm_iff_mem_minimallyAllowsTermOfFinset` : the
  statement that `minimallyAllowsTermsOfFinset S5 S10 T` contains exactly the charge spectra
  with charges in `S5` and `S10` which minimally allow the potential term `T`.

## iii. Table of contents

- A. Construction of set of charges which minimally allow a potential term
  - A.1. Preliminary: Multisets from finite sets
    - A.1.1. Multisets of cardinality `1`
    - A.1.2. Multisets of cardinality `2`
    - A.1.3. Multisets of cardinality `3`
  - A.2. `minimallyAllowsTermsOfFinset`: the set of charges which minimally allow a potential term
  - A.3. Showing `minimallyAllowsTermsOfFinset` has charges in given sets
- B. Proving the `minimallyAllowsTermsOfFinset` is set of charges which minimally allow a term
  - B.1. An element of `minimallyAllowsTermsOfFinset` is of the form `allowsTermForm`
  - B.2. Every element of `minimallyAllowsTermsOfFinset` allows the term
  - B.3. Every element of `minimallyAllowsTermsOfFinset` minimally allows the term
  - B.4. Every charge spectra which minimally allows term is in `minimallyAllowsTermsOfFinset`
  - B.5. In `minimallyAllowsTermsOfFinset` iff minimally allowing term
- C. Other properties of `minimallyAllowsTermsOfFinset`
  - C.1. Monotonicity of `minimallyAllowsTermsOfFinset` in allowed sets of charges
  - C.2. Not phenomenologically constrained if in `minimallyAllowsTermsOfFinset` for topYukawa

## iv. References

There are no known references for the material in this module.

-/
namespace SuperSymmetry

namespace SU5

namespace ChargeSpectrum

variable {𝓩 : Type}

/-!

## A. Construction of set of charges which minimally allow a potential term

We start with the construction of the set of charges which minimally allow a potential term,
and then later prover properties about this set.
The set we will define is `minimallyAllowsTermsOfFinset`, the construction of
which relies on some preliminary results.

-/

/-!

### A.1. Preliminary: Multisets from finite sets

We construct the multisets of cardinality `1`, `2` and `3` which
contain elements of finite set `s`.

-/

/-!

#### A.1.1. Multisets of cardinality `1`

-/

/-- The multisets of cardinality `1` containing elements from a finite set `s`. -/
def toMultisetsOne (s : Finset 𝓩) : Multiset (Multiset 𝓩) :=
  let X1 := (s.powersetCard 1).val.map fun X => X.val
  X1

@[simp]
lemma mem_toMultisetsOne_iff [DecidableEq 𝓩] {s : Finset 𝓩} (X : Multiset 𝓩) :
    X ∈ toMultisetsOne s ↔ X.toFinset ⊆ s ∧ X.card = 1 := by
  simp [toMultisetsOne]
  intro h
  rw [Multiset.card_eq_one] at h
  obtain ⟨x, h1, h2⟩ := h
  simp

/-!

#### A.1.2. Multisets of cardinality `2`

-/

/-- The multisets of cardinality `2` containing elements from a finite set `s`. -/
def toMultisetsTwo (s : Finset 𝓩) : Multiset (Multiset 𝓩) :=
  let X1 := (s.powersetCard 1).val.map (fun X => X.val.bind (fun x => Multiset.replicate 2 x))
  let X2 := (s.powersetCard 2).val.map fun X => X.val
  X1 + X2

@[simp]
lemma mem_toMultisetsTwo_iff [DecidableEq 𝓩] {s : Finset 𝓩} (X : Multiset 𝓩) :
    X ∈ toMultisetsTwo s ↔ X.toFinset ⊆ s ∧ X.card = 2 := by
  simp [toMultisetsTwo]
  constructor
  · intro h
    rcases h with ⟨a, ⟨hasub, hacard⟩, hbind⟩ | ⟨h1, hcard⟩
    · rw [Finset.card_eq_one] at hacard
      obtain ⟨a, rfl⟩ := hacard
      simp at hbind
      subst hbind
      simpa using hasub
    · simp_all only [and_true]
      refine Finset.subset_def.mpr ?_
      simp only [Multiset.toFinset_val, Multiset.dedup_subset']
      exact Multiset.subset_of_le h1
  · intro ⟨hsub, hcard⟩
    simp_all
    rw [Multiset.card_eq_two] at hcard
    obtain ⟨a, b, rfl⟩ := hcard
    by_cases hab : a = b
    · subst hab
      left
      use {a}
      simpa using hsub
    · right
      refine (Multiset.le_iff_subset ?_).mpr ?_
      · simpa using hab
      · exact Multiset.dedup_subset'.mp hsub

/-!

#### A.1.3. Multisets of cardinality `3`

-/

/-- The multisets of cardinality `3` containing elements from a finite set `s`. -/
def toMultisetsThree [DecidableEq 𝓩] (s : Finset 𝓩) : Multiset (Multiset 𝓩) :=
  let X1 := (s.powersetCard 1).val.map (fun X => X.val.bind (fun x => Multiset.replicate 3 x))
  let X2 := s.val.bind (fun x => (s \ {x}).val.map (fun y => {x} + Multiset.replicate 2 y))
  let X3 := (s.powersetCard 3).val.map fun X => X.val
  X1 + X2 + X3

@[simp]
lemma mem_toMultisetsThree_iff [DecidableEq 𝓩] {s : Finset 𝓩} (X : Multiset 𝓩) :
    X ∈ toMultisetsThree s ↔ X.toFinset ⊆ s ∧ X.card = 3 := by
  simp [toMultisetsThree]
  constructor
  · intro h
    rw [or_assoc] at h
    rcases h with ⟨a, ⟨hasub, hacard⟩, hbind⟩ | ⟨a, ha, ⟨b, hb, rfl⟩⟩ | ⟨h1, hcard⟩
    · rw [Finset.card_eq_one] at hacard
      obtain ⟨a, rfl⟩ := hacard
      simp at hbind
      subst hbind
      simpa using hasub
    · simp only [Multiset.toFinset_cons, Multiset.toFinset_singleton, Finset.mem_insert,
      Finset.mem_singleton, or_true, Finset.insert_eq_of_mem, Multiset.card_cons,
      Multiset.card_singleton, Nat.reduceAdd, and_true]
      refine Finset.insert_subset ha ?_
      rw [← @Multiset.mem_toFinset] at hb
      simp at hb
      simp only [Finset.singleton_subset_iff]
      exact Finset.mem_of_mem_erase hb
    · simp_all only [and_true]
      refine Finset.subset_def.mpr ?_
      simp only [Multiset.toFinset_val, Multiset.dedup_subset']
      exact Multiset.subset_of_le h1
  · intro ⟨hsub, hcard⟩
    simp_all
    rw [Multiset.card_eq_three] at hcard
    obtain ⟨a, b, c, rfl⟩ := hcard
    by_cases hab : a = b
    · subst hab
      left
      by_cases hac : a = c
      · subst hac
        left
        use {a}
        simpa using hsub
      · right
        simp [@Finset.insert_subset_iff] at hsub
        use c
        simp_all
        use a
        apply And.intro
        · refine (Multiset.mem_erase_of_ne hac).mpr ?_
          simp_all
        · simp
          rw [← Multiset.insert_eq_cons, Multiset.pair_comm c a]
          simp
    · rw [or_assoc]
      right
      by_cases hac : a = c
      · subst hac
        simp [@Finset.insert_subset_iff] at hsub
        left
        use b
        simp_all
        use a
        simp only [and_true]
        refine (Multiset.mem_erase_of_ne (by omega)).mpr ?_
        simp_all
      · by_cases hbc : b = c
        · subst hbc
          left
          simp [@Finset.insert_subset_iff] at hsub
          use a
          simp_all
          use b
          apply And.intro
          · refine (Multiset.mem_erase_of_ne (fun h => hac h.symm)).mpr ?_
            simp_all
          exact Multiset.cons_swap b a {b}
        · right
          refine (Multiset.le_iff_subset ?_).mpr ?_
          · simpa using ⟨⟨hab, hac⟩, hbc⟩
          · exact Multiset.dedup_subset'.mp hsub
/-!

### A.2. `minimallyAllowsTermsOfFinset`: the set of charges which minimally allow a potential term

Given the construction of the multisets above we can now define the set of charges
which minimally allow a potential term.

We will prove it has the desired properties later in this module.

-/

open PotentialTerm

variable {𝓩 : Type} [DecidableEq 𝓩] [AddCommGroup 𝓩]

/-- The multiset of all charges within `ofFinset S5 S10` which minimally allow the
  potential term `T`. -/
def minimallyAllowsTermsOfFinset (S5 S10 : Finset 𝓩) :
    (T : PotentialTerm) → Multiset (ChargeSpectrum 𝓩)
  | μ =>
    let SqHd := S5.val
    let SqHu := S5.val
    let prod := SqHd ×ˢ (SqHu)
    let Filt := prod.filter (fun x => - x.1 + x.2 = 0)
    (Filt.map (fun x => ⟨x.1, x.2, ∅, ∅⟩))
  | K2 =>
    let SqHd := S5.val
    let SqHu := S5.val
    let Q10 := toMultisetsOne S10
    let prod := SqHd ×ˢ (SqHu ×ˢ Q10)
    let Filt := prod.filter (fun x => x.1 + x.2.1 + x.2.2.sum = 0)
    (Filt.map (fun x => ⟨x.1, x.2.1, ∅, x.2.2.toFinset⟩))
  | K1 =>
    let Q5 := toMultisetsOne S5
    let Q10 := toMultisetsTwo S10
    let Prod := Q5 ×ˢ Q10
    let Filt := Prod.filter (fun x => - x.1.sum + x.2.sum = 0)
    (Filt.map (fun x => ⟨none, none, x.1.toFinset, x.2.toFinset⟩))
  | W4 =>
    let SqHd := S5.val
    let SqHu := S5.val
    let Q5 := toMultisetsOne S5
    let prod := SqHd ×ˢ (SqHu ×ˢ Q5)
    let Filt := prod.filter (fun x => x.1 - 2 • x.2.1 + x.2.2.sum = 0)
    (Filt.map (fun x => ⟨x.1, x.2.1, x.2.2.toFinset, ∅⟩))
  | W3 =>
    let SqHu := S5.val
    let Q5 := toMultisetsTwo S5
    let prod := SqHu ×ˢ Q5
    let Filt := prod.filter (fun x => - 2 • x.1 + x.2.sum = 0)
    (Filt.map (fun x => ⟨none, x.1, x.2.toFinset, ∅⟩))
  | W2 =>
    let SqHd := S5.val
    let Q10 := toMultisetsThree S10
    let prod := SqHd ×ˢ Q10
    let Filt := prod.filter (fun x => x.1 + x.2.sum = 0)
    (Filt.map (fun x => ⟨x.1, none, ∅, x.2.toFinset⟩)).filter fun x => MinimallyAllowsTerm x W2
  | W1 =>
    let Q5 := toMultisetsOne S5
    let Q10 := toMultisetsThree S10
    let Prod := Q5 ×ˢ Q10
    let Filt := Prod.filter (fun x => x.1.sum + x.2.sum = 0)
    (Filt.map (fun x =>
      ⟨none, none, x.1.toFinset, x.2.toFinset⟩)).filter fun x => MinimallyAllowsTerm x W1
  | Λ =>
    let Q5 := toMultisetsTwo S5
    let Q10 := toMultisetsOne S10
    let Prod := Q5 ×ˢ Q10
    let Filt := Prod.filter (fun x => x.1.sum + x.2.sum = 0)
    (Filt.map (fun x => ⟨none, none, x.1.toFinset, x.2.toFinset⟩))
  | β =>
    let SqHu := S5.val
    let Q5 := toMultisetsOne S5
    let prod := SqHu ×ˢ Q5
    let Filt := prod.filter (fun x => - x.1 + x.2.sum = 0)
    (Filt.map (fun x => ⟨none, x.1, x.2.toFinset, ∅⟩))
  | topYukawa =>
    let SqHu := S5.val
    let Q10 := toMultisetsTwo S10
    let prod := SqHu ×ˢ Q10
    let Filt := prod.filter (fun x => - x.1 + x.2.sum = 0)
    (Filt.map (fun x => ⟨none, x.1, ∅, x.2.toFinset⟩))
  | bottomYukawa =>
    let SqHd := S5.val
    let Q5 := toMultisetsOne S5
    let Q10 := toMultisetsOne S10
    let prod := SqHd ×ˢ (Q5 ×ˢ Q10)
    let Filt := prod.filter (fun x => x.1 + x.2.1.sum + x.2.2.sum = 0)
    (Filt.map (fun x => ⟨x.1, none,x.2.1.toFinset, x.2.2.toFinset⟩))

/-!

### A.3. Showing `minimallyAllowsTermsOfFinset` has charges in given sets

We show that every element of `minimallyAllowsTermsOfFinset S5 S10 T` is in `ofFinset S5 S10`.
That is every element of `minimallyAllowsTermsOfFinset S5 S10 T` has charges
in the sets `S5` and `S10`.

-/

lemma mem_ofFinset_of_mem_minimallyAllowsTermOfFinset {S5 S10 : Finset 𝓩} {T : PotentialTerm}
    {x : ChargeSpectrum 𝓩} (hx : x ∈ minimallyAllowsTermsOfFinset S5 S10 T) :
    x ∈ ofFinset S5 S10 := by
  cases T
  all_goals
    simp [minimallyAllowsTermsOfFinset] at hx
  case' W1 | W2 => have hx := hx.1
  case' μ | β | W1 | W2 | W3 | K1 | topYukawa | Λ => obtain ⟨a, b, h, rfl⟩ := hx
  case' bottomYukawa | K2 | W4 => obtain ⟨a, b, c, h, rfl⟩ := hx
  all_goals
    try rw [Multiset.card_eq_one] at h
    try rw [Multiset.card_eq_two] at h
    try rw [Multiset.card_eq_three] at h
  case' W1 =>
    obtain ⟨q51, rfl⟩ := h.1.1.2
    obtain ⟨q101, q102, q103, rfl⟩ := h.1.2.2
  case' W2 =>
    obtain ⟨q101, q102, q103, rfl⟩ := h.1.2.2
  case' W3 =>
    obtain ⟨q51, q52, rfl⟩ := h.1.2.2
  case' W4 =>
    obtain ⟨q51, rfl⟩ := h.1.2.2.2
  case' K1 =>
    obtain ⟨q51, rfl⟩ := h.1.1.2
    obtain ⟨q101, q102, rfl⟩ := h.1.2.2
  case' K2 =>
    obtain ⟨q101, rfl⟩ := h.1.2.2.2
  case' topYukawa =>
    obtain ⟨q101, q102, rfl⟩ := h.1.2.2
  case' bottomYukawa =>
    obtain ⟨q51, rfl⟩ := h.1.2.1.2
    rw [Multiset.card_eq_one] at h
    obtain ⟨q101, rfl⟩ := h.1.2.2.2
  case' Λ =>
    obtain ⟨q101, rfl⟩ := h.1.2.2
    obtain ⟨q51, q52, rfl⟩ := h.1.1.2
  case' β =>
    obtain ⟨q51, rfl⟩ := h.1.2.2
  all_goals
    rw [mem_ofFinset_iff]
    simp_all

lemma minimallyAllowsTermOfFinset_subset_ofFinset {S5 S10 : Finset 𝓩} {T : PotentialTerm} :
    minimallyAllowsTermsOfFinset S5 S10 T ⊆ (ofFinset S5 S10).val := by
  refine Multiset.subset_iff.mpr (fun x hx => ?_)
  rw [Finset.mem_val]
  exact mem_ofFinset_of_mem_minimallyAllowsTermOfFinset hx

/-!

## B. Proving the `minimallyAllowsTermsOfFinset` is set of charges which minimally allow a term

We now prove that `minimallyAllowsTermsOfFinset` has the property
that all charges spectra with charges in the sets `S5` and `S10`
which minimally allow the potential term `T` are in
`minimallyAllowsTermsOfFinset S5 S10 T`, and vice versa.

-/

/-!

### B.1. An element of `minimallyAllowsTermsOfFinset` is of the form `allowsTermForm`

We show that every element of `minimallyAllowsTermsOfFinset S5 S10 T` is of the form
`allowsTermForm a b c T` for some `a`, `b` and `c`.

-/
lemma eq_allowsTermForm_of_mem_minimallyAllowsTermOfFinset {S5 S10 : Finset 𝓩} {T : PotentialTerm}
    {x : ChargeSpectrum 𝓩} (hx : x ∈ minimallyAllowsTermsOfFinset S5 S10 T) :
    ∃ a b c, x = allowsTermForm a b c T := by
  cases T
  all_goals
    simp [minimallyAllowsTermsOfFinset] at hx
  case μ =>
    obtain ⟨a, b, ⟨⟨ha, hb⟩, hsum⟩, rfl⟩ := hx
    simp_all [allowsTermForm]
    grind
  case β =>
    obtain ⟨a, b, ⟨⟨ha, ⟨hb, hbcard⟩⟩, hsum⟩, rfl⟩ := hx
    obtain ⟨c, rfl⟩ := Multiset.card_eq_one.mp hbcard
    simp_all [allowsTermForm]
    grind
  case K1 =>
    obtain ⟨a, b, ⟨⟨⟨ha, hacard⟩, ⟨hb, hbcard⟩⟩, hsum⟩, rfl⟩ := hx
    obtain ⟨c, rfl⟩ := Multiset.card_eq_one.mp hacard
    obtain ⟨d, e, rfl⟩ := Multiset.card_eq_two.mp hbcard
    simp_all [allowsTermForm]
    use -c
    simp only [neg_neg, true_and] at ⊢ hsum
    use d
    congr
    grind
  case Λ =>
    obtain ⟨a, b, ⟨⟨⟨ha, hacard⟩, ⟨hb, hbcard⟩⟩, hsum⟩, rfl⟩ := hx
    obtain ⟨c, d, rfl⟩ := Multiset.card_eq_two.mp hacard
    obtain ⟨e, rfl⟩ := Multiset.card_eq_one.mp hbcard
    simp_all [allowsTermForm]
    use c, d
    simp_all
    grind
  case W1 =>
    obtain ⟨⟨a, b, ⟨⟨⟨ha, hacard⟩, ⟨hb, hbcard⟩⟩, hsum⟩, rfl⟩, _⟩ := hx
    obtain ⟨c, rfl⟩ := Multiset.card_eq_one.mp hacard
    obtain ⟨e, d, f, rfl⟩ := Multiset.card_eq_three.mp hbcard
    simp_all [allowsTermForm]
    use e, d, f
    simp_all
    grind
  case W2 =>
    obtain ⟨⟨a, b, ⟨⟨ha, ⟨hb, hbcard⟩⟩, hsum⟩, rfl⟩, _⟩ := hx
    obtain ⟨e, d, f, rfl⟩ := Multiset.card_eq_three.mp hbcard
    simp_all [allowsTermForm]
    use e, d, f
    simp_all
    grind
  case W3 =>
    obtain ⟨a, b, ⟨⟨ha, ⟨hb, hbcard⟩⟩, hsum⟩, rfl⟩ := hx
    obtain ⟨c, d, rfl⟩ := Multiset.card_eq_two.mp hbcard
    simp_all [allowsTermForm]
    use -a
    simp_all
    use c
    congr
    trans d - 0
    · simp
    rw [← hsum]
    abel
  case W4 =>
    obtain ⟨a, b, c, ⟨⟨ha, ⟨hb, hc, hcard⟩⟩, hsum⟩, rfl⟩ := hx
    obtain ⟨d, rfl⟩ := Multiset.card_eq_one.mp hcard
    simp_all [allowsTermForm]
    use -b
    simp_all
    grind
  case K2 =>
    obtain ⟨a, b, c, ⟨⟨ha, ⟨hb, hc, hcard⟩⟩, hsum⟩, rfl⟩ := hx
    obtain ⟨d, rfl⟩ := Multiset.card_eq_one.mp hcard
    simp_all [allowsTermForm]
    grind
  case topYukawa =>
    obtain ⟨a, b, ⟨⟨ha, ⟨hb, hbcard⟩⟩, hsum⟩, rfl⟩ := hx
    obtain ⟨c, d, rfl⟩ := Multiset.card_eq_two.mp hbcard
    simp_all [allowsTermForm]
    use -a
    simp_all
    use c
    congr
    grind
  case bottomYukawa =>
    obtain ⟨a, b, c, ⟨⟨ha, ⟨⟨hb, hbcard⟩, hc, hcard⟩⟩, hsum⟩, rfl⟩ := hx
    obtain ⟨e, rfl⟩ := Multiset.card_eq_one.mp hcard
    obtain ⟨d, rfl⟩ := Multiset.card_eq_one.mp hbcard
    simp_all [allowsTermForm]
    grind

/-!

### B.2. Every element of `minimallyAllowsTermsOfFinset` allows the term

We show that every element of `minimallyAllowsTermsOfFinset S5 S10 T` allows the term `T`.

-/

lemma allowsTerm_of_mem_minimallyAllowsTermOfFinset {S5 S10 : Finset 𝓩} {T : PotentialTerm}
    {x : ChargeSpectrum 𝓩} (hx : x ∈ minimallyAllowsTermsOfFinset S5 S10 T) :
    x.AllowsTerm T := by
  obtain ⟨a, b, c, rfl⟩ := eq_allowsTermForm_of_mem_minimallyAllowsTermOfFinset hx
  exact allowsTermForm_allowsTerm

/-!

### B.3. Every element of `minimallyAllowsTermsOfFinset` minimally allows the term

We make the above condition stronger, showing that every element of
`minimallyAllowsTermsOfFinset S5 S10 T` minimally allows the term `T`.

-/

lemma minimallyAllowsTerm_of_mem_minimallyAllowsTermOfFinset {S5 S10 : Finset 𝓩}
    {T : PotentialTerm} {x : ChargeSpectrum 𝓩}
    (hx : x ∈ minimallyAllowsTermsOfFinset S5 S10 T) :
    x.MinimallyAllowsTerm T := by
  by_cases hT : T ≠ W1 ∧ T ≠ W2
  · obtain ⟨a, b, c, rfl⟩ := eq_allowsTermForm_of_mem_minimallyAllowsTermOfFinset hx
    exact allowsTermForm_minimallyAllowsTerm hT
  · simp at hT
    by_cases h : T = W1
    · subst h
      simp [minimallyAllowsTermsOfFinset] at hx
      exact hx.2
    · simp_all
      subst hT
      simp [minimallyAllowsTermsOfFinset] at hx
      exact hx.2

/-!

### B.4. Every charge spectra which minimally allows term is in `minimallyAllowsTermsOfFinset`

We show that every charge spectra which minimally allows term `T` and has charges
in the sets `S5` and `S10` is in `minimallyAllowsTermsOfFinset S5 S10 T`.

-/
lemma mem_minimallyAllowsTermOfFinset_of_minimallyAllowsTerm {S5 S10 : Finset 𝓩}
    {T : PotentialTerm} (x : ChargeSpectrum 𝓩) (h : x.MinimallyAllowsTerm T)
    (hx : x ∈ ofFinset S5 S10) :
    x ∈ minimallyAllowsTermsOfFinset S5 S10 T := by
  obtain ⟨a, b, c, rfl⟩ := eq_allowsTermForm_of_minimallyAllowsTerm h
  cases T
  all_goals
    simp [allowsTermForm, minimallyAllowsTermsOfFinset]
    rw [mem_ofFinset_iff] at hx
  case μ =>
    simp_all [allowsTermForm]
  case β =>
    use {a}
    simp_all [allowsTermForm]
  case Λ =>
    use {a, b}, {- a - b}
    simp_all [allowsTermForm]
  case W1 =>
    apply And.intro
    · use {- a - b - c}, {a, b, c}
      simp_all [allowsTermForm]
      abel
    · exact h
  case W2 =>
    apply And.intro
    · use {a, b, c}
      simp_all [allowsTermForm]
      abel
    · exact h
  case W3 =>
    use {b, - b - 2 • a}
    simp_all [allowsTermForm]
    abel
  case W4 =>
    use {c}
    simp_all [allowsTermForm]
  case K1 =>
    use {-a}, {b, - a - b}
    simp_all [allowsTermForm]
  case K2 =>
    use {- a - b}
    simp_all [allowsTermForm]
  case topYukawa =>
    use {b, - a - b}
    simp_all [allowsTermForm]
  case bottomYukawa =>
    use {b}, {- a - b}
    simp_all [allowsTermForm]

/-!

### B.5. In `minimallyAllowsTermsOfFinset` iff minimally allowing term

We now show the key result of this section, that a charge spectrum `x`
is in `minimallyAllowsTermsOfFinset S5 S10 T` if and only if
it minimally allows the term `T`, provided it is in `ofFinset S5 S10`.

-/

lemma minimallyAllowsTerm_iff_mem_minimallyAllowsTermOfFinset
    {S5 S10 : Finset 𝓩} {T : PotentialTerm}
    {x : ChargeSpectrum 𝓩} (hx : x ∈ ofFinset S5 S10) :
    x.MinimallyAllowsTerm T ↔ x ∈ minimallyAllowsTermsOfFinset S5 S10 T := by
  constructor
  · intro h
    exact mem_minimallyAllowsTermOfFinset_of_minimallyAllowsTerm x h hx
  · intro h
    exact minimallyAllowsTerm_of_mem_minimallyAllowsTermOfFinset h

/-!

## C. Other properties of `minimallyAllowsTermsOfFinset`

We show two other properties of `minimallyAllowsTermsOfFinset`.

-/

/-!

### C.1. Monotonicity of `minimallyAllowsTermsOfFinset` in allowed sets of charges

-/

lemma minimallyAllowsTermOfFinset_subset_of_subset {S5 S5' S10 S10' : Finset 𝓩} {T : PotentialTerm}
    (h5 : S5' ⊆ S5) (h10 : S10' ⊆ S10) :
    minimallyAllowsTermsOfFinset S5' S10' T ⊆ minimallyAllowsTermsOfFinset S5 S10 T := by
  intro x hx
  have h1 : x ∈ ofFinset S5' S10' := mem_ofFinset_of_mem_minimallyAllowsTermOfFinset hx
  rw [← minimallyAllowsTerm_iff_mem_minimallyAllowsTermOfFinset
    (ofFinset_subset_of_subset h5 h10 h1)]
  exact (minimallyAllowsTerm_iff_mem_minimallyAllowsTermOfFinset h1).mpr hx

/-!

### C.2. Not phenomenologically constrained if in `minimallyAllowsTermsOfFinset` for topYukawa

We show that every term which is in `minimallyAllowsTermsOfFinset S5 S10 topYukawa` is not
phenomenologically constrained.

-/

lemma not_isPhenoConstrained_of_minimallyAllowsTermsOfFinset_topYukawa
    {S5 S10 : Finset 𝓩} {x : ChargeSpectrum 𝓩}
    (hx : x ∈ minimallyAllowsTermsOfFinset S5 S10 topYukawa) :
    ¬ x.IsPhenoConstrained := by
  simp [minimallyAllowsTermsOfFinset] at hx
  obtain ⟨qHu, Q10, h1, rfl⟩ := hx
  simp [IsPhenoConstrained, AllowsTerm, mem_ofPotentialTerm_iff_mem_ofPotentialTerm,
    ofPotentialTerm']

end ChargeSpectrum

end SU5

end SuperSymmetry
