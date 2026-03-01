/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Option
import PhysLean.Particles.SuperSymmetry.SU5.Potential
/-!

# Charge Spectrum

## i. Overview

In this module we define the charge spectrum of a `SU(5)` SUSY GUT theory with
additional charges (usually `U(1)`) valued in `𝓩` satisfying the condition of:
- The optional existence of a `Hd` particle in the `bar 5` representation.
- The optional existence of a `Hu` particle in the `5` representation.
- The optional existence of matter in the `bar 5` representation.
- The optional existence of matter in the `10` representation.

The charge spectrum contains the information of the *unique* charges of each type of particle
present in theory. Importantly, the charge spectrum does not contain information
about the multiplicity of those charges.

With just the charge spectrum of the theory it is possible to put a number of constraints
on the theory, most notably phenomenological constraints.

By keeping the presence of `Hd` and `Hu` optional, we can define a number of useful properties
of the charge spectrum, which can help in searching for viable theories.

## ii. Key results

- `ChargeSpectrum 𝓩` : The type of charge spectra with charges of type `𝓩`, which is usually
  `ℤ`.

## iii. Table of contents

- A. The definition of the charge spectrum
  - A.1. Extensionality properties
  - A.2. Relation to products
  - A.3. Rendering
- B. The subset relation
- C. The empty charge spectrum
- D. The cardinality of a charge spectrum
- E. The power set of a charge spectrum
- F. Finite sets of charge spectra with values
  - F.1. Cardinality of finite sets of charge spectra with values

## iv. References

There are no known references for charge spectra in the literature.
They were created specifically for the purpose of PhysLean.

-/

namespace SuperSymmetry

namespace SU5

/-!

## A. The definition of the charge spectrum

-/

/-- The type such that an element corresponds to the collection of
  charges associated with the matter content of the theory.
  The order of charges is implicitly taken to be `qHd`, `qHu`, `Q5`, `Q10`.

  The `Q5` and `Q10` charges are represented by `Finset` rather than
  `Multiset`, so multiplicity is not included.

  This is defined for a general type `𝓩`, which could be e.g.
- `ℤ` in the case of `U(1)`,
- `ℤ × ℤ` in the case of `U(1) × U(1)`,
- `Fin 2` in the case of `ℤ₂` etc.
-/
structure ChargeSpectrum (𝓩 : Type := ℤ) where
  /-- The charge of the `Hd` particle. -/
  qHd : Option 𝓩
  /-- The negative of the charge of the `Hu` particle. That is to say,
    the charge of the `Hu` when considered in the 5-bar representation. -/
  qHu : Option 𝓩
  /-- The finite set of charges of the matter fields in the `Q5` representation. -/
  Q5 : Finset 𝓩
  /-- The finite set of charges of the matter fields in the `Q10` representation. -/
  Q10 : Finset 𝓩

namespace ChargeSpectrum

variable {𝓩 : Type}

/-!

### A.1. Extensionality properties

We prove extensionality properties for `ChargeSpectrum 𝓩`, that is
conditions of when two elements of `ChargeSpectrum 𝓩` are equal.
We also show that when `𝓩` has decidable equality, so does `ChargeSpectrum 𝓩`.

-/

lemma eq_of_parts {x y : ChargeSpectrum 𝓩} (h1 : x.qHd = y.qHd) (h2 : x.qHu = y.qHu)
    (h3 : x.Q5 = y.Q5) (h4 : x.Q10 = y.Q10) : x = y := by
  cases x
  cases y
  simp_all

lemma eq_iff {x y : ChargeSpectrum 𝓩} :
    x = y ↔ x.qHd = y.qHd ∧ x.qHu = y.qHu ∧ x.Q5 = y.Q5 ∧ x.Q10 = y.Q10 := by
  constructor
  · intro h
    subst h
    simp
  · rintro ⟨h1, h2, h3, h4⟩
    exact eq_of_parts h1 h2 h3 h4

instance [DecidableEq 𝓩] : DecidableEq (ChargeSpectrum 𝓩) := fun _ _ =>
  decidable_of_iff _ eq_iff.symm

/-!

### A.2. Relation to products

We show that `ChargeSpectrum 𝓩` is equivalent to the product
`Option 𝓩 × Option 𝓩 × Finset 𝓩 × Fin 𝓩`.

In an old implementation this was definitionally true, it is not so now.

-/

/-- The explicit casting of a term of type `Charges 𝓩` to a term of
  `Option 𝓩 × Option 𝓩 × Finset 𝓩 × Finset 𝓩`. -/
def toProd : ChargeSpectrum 𝓩 ≃ Option 𝓩 × Option 𝓩 × Finset 𝓩 × Finset 𝓩 where
  toFun x := (x.qHd, x.qHu, x.Q5, x.Q10)
  invFun x := ⟨x.1, x.2.1, x.2.2.1, x.2.2.2⟩
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl

/-!

### A.3. Rendering

-/

unsafe instance [Repr 𝓩] : Repr (ChargeSpectrum 𝓩) where
  reprPrec x _ := match x with
    | ⟨qHd, qHu, Q5, Q10⟩ =>
      let s1 := reprStr qHd
      let s2 := reprStr qHu
      let s5 := reprStr Q5
      let s10 := reprStr Q10
      s!"⟨{s1}, {s2}, {s5}, {s10}⟩"

/-!

## B. The subset relation

We define a `HasSubset` and `HasSSubset` instance on `ChargeSpectrum 𝓩`.

-/

instance hasSubset : HasSubset (ChargeSpectrum 𝓩) where
  Subset x y :=
    x.qHd.toFinset ⊆ y.qHd.toFinset ∧
    x.qHu.toFinset ⊆ y.qHu.toFinset ∧
    x.Q5 ⊆ y.Q5 ∧
    x.Q10 ⊆ y.Q10

instance hasSSubset : HasSSubset (ChargeSpectrum 𝓩) where
  SSubset x y := x ⊆ y ∧ x ≠ y

instance subsetDecidable [DecidableEq 𝓩] (x y : ChargeSpectrum 𝓩) : Decidable (x ⊆ y) :=
  instDecidableAnd

lemma subset_def {x y : ChargeSpectrum 𝓩} : x ⊆ y ↔ x.qHd.toFinset ⊆ y.qHd.toFinset ∧
    x.qHu.toFinset ⊆ y.qHu.toFinset ∧ x.Q5 ⊆ y.Q5 ∧ x.Q10 ⊆ y.Q10 := by
  rfl

@[simp, refl]
lemma subset_refl (x : ChargeSpectrum 𝓩) : x ⊆ x := ⟨by rfl, by rfl, by rfl, by rfl⟩

lemma _root_.Option.toFinset_inj {x y : Option 𝓩} :
    x = y ↔ x.toFinset = y.toFinset := by
  match x, y with
  | none, none => simp [Option.toFinset]
  | none, some a =>
    rw [show (none = some a) ↔ False by simp]
    simp only [Option.toFinset_none, Option.toFinset_some, false_iff, ne_eq]
    rw [Finset.eq_singleton_iff_unique_mem]
    simp
  | some _, none => simp [Option.toFinset]
  | some _, some _ => simp [Option.toFinset]

lemma subset_trans {x y z : ChargeSpectrum 𝓩} (hxy : x ⊆ y) (hyz : y ⊆ z) : x ⊆ z := by
  simp_all [Subset]

lemma subset_antisymm {x y : ChargeSpectrum 𝓩} (hxy : x ⊆ y) (hyx : y ⊆ x) : x = y := by
  rw [Subset] at hxy hyx
  dsimp [hasSubset] at hxy hyx
  rcases x with ⟨x1, x2, x3, x4⟩
  rcases y with ⟨y1, y2, y3, y4⟩
  have hx1 : x1.toFinset = y1.toFinset := Finset.Subset.antisymm_iff.mpr ⟨hxy.1, hyx.1⟩
  have hx2 : x2.toFinset = y2.toFinset := Finset.Subset.antisymm_iff.mpr ⟨hxy.2.1, hyx.2.1⟩
  have hx3 : x3 = y3 := Finset.Subset.antisymm_iff.mpr ⟨hxy.2.2.1, hyx.2.2.1⟩
  have hx4 : x4 = y4 := Finset.Subset.antisymm_iff.mpr ⟨hxy.2.2.2, hyx.2.2.2⟩
  rw [← Option.toFinset_inj] at hx1 hx2
  simp_all

/-!

## C. The empty charge spectrum

-/

instance emptyInst : EmptyCollection (ChargeSpectrum 𝓩) where
  emptyCollection := ⟨none, none, {}, {}⟩

@[simp]
lemma empty_subset (x : ChargeSpectrum 𝓩) : ∅ ⊆ x := by
  simp [Subset, emptyInst]

@[simp]
lemma subset_of_empty_iff_empty {x : ChargeSpectrum 𝓩} :
    x ⊆ ∅ ↔ x = ∅ := by
  constructor
  · intro h
    apply subset_antisymm
    · exact h
    · exact empty_subset x
  · intro h
    subst h
    simp

@[simp]
lemma empty_qHd : (∅ : ChargeSpectrum 𝓩).qHd = none := by
  simp [emptyInst]

@[simp]
lemma empty_qHu : (∅ : ChargeSpectrum 𝓩).qHu = none := by
  simp [emptyInst]

@[simp]
lemma empty_Q5 : (∅ : ChargeSpectrum 𝓩).Q5 = ∅ := by
  simp [emptyInst]

@[simp]
lemma empty_Q10 : (∅ : ChargeSpectrum 𝓩).Q10 = ∅ := by
  simp [emptyInst]

/-!

## D. The cardinality of a charge spectrum

-/

/-- The cardinality of a `Charges` is defined to be the sum of the cardinalities
  of each of the underlying finite sets of charges, with `Option ℤ` turned to finsets. -/
def card (x : ChargeSpectrum 𝓩) : Nat :=
  x.qHu.toFinset.card + x.qHd.toFinset.card + x.Q5.card + x.Q10.card

@[simp]
lemma card_empty : card (∅ : ChargeSpectrum 𝓩) = 0 := by
  simp [card, emptyInst]

lemma card_mono {x y : ChargeSpectrum 𝓩} (h : x ⊆ y) : card x ≤ card y := by
  simp [hasSubset] at h
  have h1 := Finset.card_le_card h.1
  have h2 := Finset.card_le_card h.2.1
  have h3 := Finset.card_le_card h.2.2.1
  have h4 := Finset.card_le_card h.2.2.2
  simp [card]
  omega

lemma eq_of_subset_card {x y : ChargeSpectrum 𝓩} (h : x ⊆ y) (hcard : card x = card y) : x = y := by
  simp [card] at hcard
  have h1 := Finset.card_le_card h.1
  have h2 := Finset.card_le_card h.2.1
  have h3 := Finset.card_le_card h.2.2.1
  have h4 := Finset.card_le_card h.2.2.2
  have h1 : x.1.toFinset = y.1.toFinset := by
    apply Finset.eq_of_subset_of_card_le h.1
    omega
  have h2 : x.qHu.toFinset = y.qHu.toFinset := by
    apply Finset.eq_of_subset_of_card_le h.2.1
    omega
  have h3 : x.Q5 = y.Q5 := by
    apply Finset.eq_of_subset_of_card_le h.2.2.1
    omega
  have h4 : x.Q10 = y.Q10 := by
    apply Finset.eq_of_subset_of_card_le h.2.2.2
    omega
  match x, y with
  | ⟨x1, x2, x3, x4⟩, ⟨y1, y2, y3, y4⟩ =>
  rw [← Option.toFinset_inj] at h1 h2
  simp_all

/-!

## E. The power set of a charge spectrum

-/

variable [DecidableEq 𝓩]

/-- The powerset of `x : Option 𝓩` defined as `{none}` if `x` is `none`
  and `{none, some y}` is `x` is `some y`. -/
def _root_.Option.powerset (x : Option 𝓩) : Finset (Option 𝓩) :=
  match x with
  | none => {none}
  | some x => {none, some x}

@[simp]
lemma _root_.Option.mem_powerset_iff {x : Option 𝓩} (y : Option 𝓩) :
    y ∈ x.powerset ↔ y.toFinset ⊆ x.toFinset :=
  match x, y with
  | none, none => by
    simp [Option.powerset]
  | none, some _ => by
    simp [Option.powerset]
  | some _, none => by
    simp [Option.powerset]
  | some _, some _ => by
    simp [Option.powerset]

/-- The powerset of a charge . Given a charge `x : Charges`
  it's powerset is the finite set of all `Charges` which are subsets of `x`. -/
def powerset (x : ChargeSpectrum 𝓩) : Finset (ChargeSpectrum 𝓩) :=
  (x.qHd.powerset.product <| x.qHu.powerset.product <| x.Q5.powerset.product <|
    x.Q10.powerset).map toProd.symm.toEmbedding

lemma mem_powerset_iff {x y : ChargeSpectrum 𝓩} :
    x ∈ powerset y ↔
    x.qHd ∈ y.qHd.powerset ∧
    x.qHu ∈ y.qHu.powerset ∧
    x.Q5 ∈ y.Q5.powerset ∧
    x.Q10 ∈ y.Q10.powerset := by
  simp [powerset, Finset.mem_product, toProd]

@[simp]
lemma mem_powerset_iff_subset {x y : ChargeSpectrum 𝓩} :
    x ∈ powerset y ↔ x ⊆ y := by
  cases x
  cases y
  simp [mem_powerset_iff, Subset]

lemma self_mem_powerset (x : ChargeSpectrum 𝓩) :
    x ∈ powerset x := by simp

lemma empty_mem_powerset (x : ChargeSpectrum 𝓩) :
    ∅ ∈ powerset x := by simp

@[simp]
lemma powerset_of_empty :
    powerset (∅ : ChargeSpectrum 𝓩) = {∅} := by
  ext x
  simp

lemma powerset_mono {x y : ChargeSpectrum 𝓩} :
    powerset x ⊆ powerset y ↔ x ⊆ y := by
  constructor
  · intro h
    rw [← mem_powerset_iff_subset]
    apply h
    simp
  · intro h z
    simp only [mem_powerset_iff_subset]
    intro h1
    exact subset_trans h1 h

lemma min_exists_inductive (S : Finset (ChargeSpectrum 𝓩)) (hS : S ≠ ∅) :
    (n : ℕ) → (hn : S.card = n) →
    ∃ y ∈ S, powerset y ∩ S = {y}
  | 0, h => by simp_all
  | 1, h => by
    rw [Finset.card_eq_one] at h
    obtain ⟨y, rfl⟩ := h
    use y
    simp
  | n + 1 + 1, h => by
    rw [← Finset.nonempty_iff_ne_empty] at hS
    obtain ⟨y, hy⟩ := hS
    have hSremo : (S.erase y).card = n + 1 := by
      rw [Finset.card_erase_eq_ite]
      simp_all
    have hSeraseNeEmpty : (S.erase y) ≠ ∅ := by
        simp only [ne_eq]
        rw [← Finset.card_eq_zero]
        omega
    obtain ⟨x, hx1, hx2⟩ := min_exists_inductive (S.erase y) hSeraseNeEmpty (n + 1) hSremo
    have hxy : x ≠ y := by
      by_contra hn
      subst hn
      simp at hx1
    by_cases hyPx : y ∈ powerset x
    · use y
      constructor
      · exact hy
      · ext z
        constructor
        · intro hz
          simp at hz
          simp only [Finset.mem_singleton]
          rw [Finset.inter_erase] at hx2
          by_cases hn : z = y
          · exact hn
          apply False.elim
          have hlz : z ∈ (x.powerset ∩ S).erase y := by
            simp [hn, hz.2]
            simp at hyPx
            exact subset_trans hz.1 hyPx
          rw [hx2] at hlz
          simp at hlz
          simp_all
          have hx : y = x := by
            apply subset_antisymm
            · exact hyPx
            · exact hz
          exact hxy (id (Eq.symm hx))
        · intro hz
          simp at hz
          subst hz
          simp_all
    · use x
      constructor
      · apply Finset.erase_subset y S
        exact hx1
      · rw [← hx2]
        ext z
        simp only [Finset.mem_inter, mem_powerset_iff_subset, Finset.mem_erase, ne_eq,
          and_congr_right_iff, iff_and_self]
        intro hzx hzS hzy
        subst hzy
        simp_all

lemma min_exists (S : Finset (ChargeSpectrum 𝓩)) (hS : S ≠ ∅) :
    ∃ y ∈ S, powerset y ∩ S = {y} := min_exists_inductive S hS S.card rfl

/-!

## F. Finite sets of charge spectra with values

We define the finite set of `ChargeSpectrum` with 5-bar and 10d representation
charges in a given finite set.

-/

/-- Given `S5 S10 : Finset 𝓩` the finite set of charges associated with
  for which the 5-bar representation charges sit in `S5` and
  the 10d representation charges sit in `S10`. -/
def ofFinset (S5 S10 : Finset 𝓩) : Finset (ChargeSpectrum 𝓩) :=
  let SqHd := {none} ∪ S5.map ⟨Option.some, Option.some_injective 𝓩⟩
  let SqHu := {none} ∪ S5.map ⟨Option.some, Option.some_injective 𝓩⟩
  let SQ5 := S5.powerset
  let SQ10 := S10.powerset
  (SqHd.product (SqHu.product (SQ5.product SQ10))).map toProd.symm.toEmbedding

lemma mem_ofFinset_iff {S5 S10 : Finset 𝓩} {x : ChargeSpectrum 𝓩} :
    x ∈ ofFinset S5 S10 ↔ x.qHd.toFinset ⊆ S5 ∧ x.qHu.toFinset ⊆ S5 ∧
      x.Q5 ⊆ S5 ∧ x.Q10 ⊆ S10 := by
  simp only [ofFinset, Finset.singleton_union, Finset.product_eq_sprod, Finset.mem_map,
    Finset.mem_product, Finset.mem_insert, Finset.mem_map, Function.Embedding.coeFn_mk,
    Finset.mem_powerset, Prod.exists]
  have hoption (x : Option 𝓩) (S : Finset 𝓩) :
      x ∈ ({none} : Finset (Option 𝓩)) ∪ S.map ⟨Option.some, Option.some_injective 𝓩⟩ ↔
      x.toFinset ⊆ S := by cases x <;> simp
  constructor
  · rintro ⟨qHd', qHu', Q5', Q10', h, rfl⟩
    simp_all [toProd]
  · intro h
    use x.qHd, x.qHu, x.Q5, x.Q10
    simp_all [toProd]

lemma mem_ofFinset_antitone (S5 S10 : Finset 𝓩)
    {x y : ChargeSpectrum 𝓩} (h : x ⊆ y) (hy : y ∈ ofFinset S5 S10) :
    x ∈ ofFinset S5 S10 := by
  rw [mem_ofFinset_iff] at hy ⊢
  simp [subset_def] at h
  exact ⟨h.1.trans hy.1, h.2.1.trans hy.2.1, h.2.2.1.trans hy.2.2.1, h.2.2.2.trans hy.2.2.2⟩

lemma ofFinset_subset_of_subset {S5 S5' S10 S10' : Finset 𝓩}
    (h5 : S5 ⊆ S5') (h10 : S10 ⊆ S10') :
    ofFinset S5 S10 ⊆ ofFinset S5' S10' := by
  intro x hx
  rw [mem_ofFinset_iff] at hx ⊢
  exact ⟨hx.1.trans h5, hx.2.1.trans h5, hx.2.2.1.trans h5, hx.2.2.2.trans h10⟩

lemma ofFinset_univ [Fintype 𝓩] (x : ChargeSpectrum 𝓩) :
    x ∈ ofFinset (Finset.univ : Finset 𝓩) (Finset.univ : Finset 𝓩) := by
  rw [mem_ofFinset_iff]
  simp

/-!

### F.1. Cardinality of finite sets of charge spectra with values

-/

/-- The cardinality of `ofFinset S5 S10`. -/
def ofFinsetCard (S5 S10 : Finset 𝓩) : ℕ :=
    (S5.card + 1) * (S5.card + 1) * (2 ^ S5.card : ℕ) * (2 ^ S10.card : ℕ)

lemma ofFinset_card_eq_ofFinsetCard (S5 S10 : Finset 𝓩) :
    (ofFinset S5 S10).card = ofFinsetCard S5 S10 := by
  simp [ofFinset, Finset.card_map, Finset.card_product, Finset.card_powerset, ofFinsetCard]
  grind

end ChargeSpectrum

end SU5

end SuperSymmetry
