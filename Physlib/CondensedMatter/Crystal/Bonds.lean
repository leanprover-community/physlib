/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.CondensedMatter.Crystal.Basic

/-!
# Bonds in a crystal

A bond connects sites in two unit cells of a crystal.

## i. Overview

A bond `⟨i, j, d⟩` joins the site with label `i` in cell `n` to the site with label `j`
in cell `n + d`. Translating both endpoints gives another copy of the same bond.

## ii. Key results

- `Bond` : a source label, a target label and the displacement between their cells.
- `Bond.Links` : the relation between sites connected by a bond.
- `Bond.reverse` : the same bond read from its target to its source.

## iii. Table of contents

- A. Bonds in a unit cell

## iv. References

* F. Göhmann, *Introduction to Solid State Physics*, lecture L3, Section 3.1, for the standard
  description of a crystal. [ref: goehmann_solid_state_2021]

-/

@[expose] public section

namespace Physlib.CondensedMatter.Crystal

variable {G : Type*} [AddCommGroup G] [AddGroup.FG G] {C : Crystal G}

/-! ## A. Bonds in a unit cell -/

/-- A bond from `source` in one cell to `target` in the cell displaced by `displacement`. -/
structure Bond (C : Crystal G) where
  /-- The site label at the start of the bond. -/
  source : C.UnitCell
  /-- The site label at the end of the bond. -/
  target : C.UnitCell
  /-- Translation from the source cell to the target cell. -/
  displacement : G

/-- Bonds can be compared when cells and unit-cell labels can be compared. -/
instance {C : Crystal G} [DecidableEq G] [DecidableEq C.UnitCell] : DecidableEq (Bond C) :=
  fun b b' => decidable_of_iff
    (b.source = b'.source ∧ b.target = b'.target ∧ b.displacement = b'.displacement)
    (by cases b; cases b'; simp)

namespace Bond

/-- Site `x` is the source and site `y` is the target of this bond. -/
def Links (b : Bond C) (x y : C.Site) : Prop :=
  x.label = b.source ∧ y.label = b.target ∧ y.cell = x.cell + b.displacement

/-- Every bond links the reference site of its source to the site its displacement points to. -/
lemma links_reference (b : Bond C) : b.Links (Site.ref b.source) ⟨b.displacement, b.target⟩ :=
  ⟨rfl, rfl, (zero_add _).symm⟩

/-- Two bonds linking the same pair of sites are equal. -/
lemma eq_of_links {b b' : Bond C} {x y : C.Site} (h : b.Links x y) (h' : b'.Links x y) :
    b = b' := by
  obtain ⟨s, t, d⟩ := b
  obtain ⟨s', t', d'⟩ := b'
  obtain ⟨hs, ht, hd⟩ := h
  obtain ⟨hs', ht', hd'⟩ := h'
  simp_all

/-- Translating the endpoints gives another copy of the same bond. -/
lemma links_vadd (b : Bond C) (a : G) (x y : C.Site) :
    b.Links (a +ᵥ x) (a +ᵥ y) ↔ b.Links x y := by
  simp only [Links, Site.vadd_def, add_assoc, add_right_inj]

/-- The same bond read from its target to its source. -/
def reverse (b : Bond C) : Bond C := ⟨b.target, b.source, -b.displacement⟩

/-- Reversing a bond twice gives the bond back. -/
@[simp] lemma reverse_reverse (b : Bond C) : b.reverse.reverse = b := by
  simp [reverse]

/-- A bond links two sites exactly when its reverse links them in the other order. -/
lemma links_reverse {b : Bond C} {x y : C.Site} : b.reverse.Links y x ↔ b.Links x y := by
  simp only [Links, reverse]
  grind

/-- A bond is trivial when it links a site to itself. -/
def IsLoop (b : Bond C) : Prop := b.source = b.target ∧ b.displacement = 0

/-- Whether a bond is trivial can be decided. -/
instance [DecidableEq G] [DecidableEq C.UnitCell] (b : Bond C) : Decidable b.IsLoop :=
  inferInstanceAs (Decidable (b.source = b.target ∧ b.displacement = 0))

/-- A bond is trivial exactly when its reverse is. -/
@[simp] lemma isLoop_reverse (b : Bond C) : b.reverse.IsLoop ↔ b.IsLoop := by
  simp only [IsLoop, reverse, neg_eq_zero]
  grind

/-- A trivial bond links a site only to itself. -/
lemma eq_of_isLoop_links {b : Bond C} (hb : b.IsLoop) {x y : C.Site} (h : b.Links x y) :
    x = y := by
  obtain ⟨hs, ht, hc⟩ := h
  exact Site.ext (by simpa [hb.2] using hc.symm) (hs.trans (hb.1.trans ht.symm))

/-- A bond that links a site to itself is trivial. -/
lemma isLoop_of_links {b : Bond C} {x : C.Site} (h : b.Links x x) : b.IsLoop := by
  obtain ⟨hs, ht, hc⟩ := h
  exact ⟨hs.symm.trans ht, by simpa using hc⟩

/-- The source and target of a bond can be checked from their site addresses. -/
instance [DecidableEq G] [DecidableEq C.UnitCell] (b : Bond C) : DecidableRel b.Links :=
  fun x y => inferInstanceAs (Decidable (x.label = b.source ∧ y.label = b.target ∧
    y.cell = x.cell + b.displacement))

end Bond

end Physlib.CondensedMatter.Crystal
