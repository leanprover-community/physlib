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

/-- Translating the endpoints gives another copy of the same bond. -/
lemma links_vadd (b : Bond C) (a : G) (x y : C.Site) :
    b.Links (a +ᵥ x) (a +ᵥ y) ↔ b.Links x y := by
  simp only [Links, Site.vadd_def, add_assoc, add_right_inj]

/-- The source and target of a bond can be checked from their site addresses. -/
instance [DecidableEq G] [DecidableEq C.UnitCell] (b : Bond C) : DecidableRel b.Links :=
  fun x y => inferInstanceAs (Decidable (x.label = b.source ∧ y.label = b.target ∧
    y.cell = x.cell + b.displacement))

end Bond

end Physlib.CondensedMatter.Crystal
