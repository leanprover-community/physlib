/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.GroupTheory.Finiteness

/-!

# Crystals, cells and sites

A crystal is a finite unit cell repeated periodically.

## i. Overview

The goal is to construct crystals such as the square, hexagonal, fcc, bcc and hcp lattices. The
standard starting point is a unit cell repeated by translations; see the reference below. We
start combinatorially, with a unit cell that repeats many times over. This periodicity is modeled
by a finitely generated abelian group `G`, written additively, with `ℤᵈ` as the prototypical
example. Each unit cell consists of finitely many things, such as atoms, spins or orbitals, which
are labeled by a type `F`. Repeating the cell gives one site `⟨n, i⟩` for every cell `n : G` and
label `i : F`. Translation acts only on the cell:

`a +ᵥ ⟨n, i⟩ = ⟨a + n, i⟩`.

A crystal with one site per cell has a single label, while the honeycomb and hcp lattices have two.

For `ℤᵈ` the sites form an infinite array, and for `(ℤ/mℤ)ᵈ` a finite array with periodic
boundary conditions. Coordinates in space, and with them distances and angles, are not part of this
description and is added in other files.

## ii. Key results

- `Crystal` : a finitely generated abelian translation group with a finite, nonempty unit cell.
- `Crystal.ofUnitCell` : the crystal obtained by repeating a labeled unit cell.
- `Crystal.Site` : a site given by its cell and unit-cell label.
- `Crystal.Site.mem_orbit_iff_label_eq` : the translates of a site are exactly the sites with the
  same label.

## iii. Table of contents

- A. The unit cell
- B. Constructing a crystal from a unit cell
- C. Sites and their finiteness
- D. Translation symmetry

## iv. References

* F. Göhmann, *Introduction to Solid State Physics*, lecture L3, Section 3.1, for the standard
  description of a crystal as translated copies of a unit cell. [ref: goehmann_solid_state_2021]

-/

@[expose] public section

namespace Physlib.CondensedMatter

/-! ## A. The unit cell -/

/-- A crystal with finitely generated abelian translation group `G` and a finite, nonempty unit
cell. The sites are one copy of each unit-cell label in every translated cell. -/
structure Crystal (G : Type*) [AddCommGroup G] [AddGroup.FG G] where
  /-- The labels of the things in one unit cell, such as atoms, spins or orbitals. -/
  UnitCell : Type*
  /-- The unit cell has finitely many labels. -/
  [finiteUnitCell : Finite UnitCell]
  /-- The unit cell has at least one label. -/
  [nonemptyUnitCell : Nonempty UnitCell]

attribute [instance] Crystal.finiteUnitCell Crystal.nonemptyUnitCell

namespace Crystal

/-! ## B. Constructing a crystal from a unit cell -/

/-- Construct a crystal by repeating a unit cell with labels `F`.
The group `G` indexes translated cells; `⟨n, i⟩` is the site with label `i` in cell `n`. -/
abbrev ofUnitCell (G : Type*) (F : Type*) [AddCommGroup G] [AddGroup.FG G]
    [Finite F] [Nonempty F] : Crystal G where
  UnitCell := F

variable {G : Type*} [AddCommGroup G] [AddGroup.FG G]

/-! ## C. Sites and their finiteness -/

/-- A site of `C`, with label `i` in cell `n`. -/
@[ext] structure Site (C : Crystal G) where
  /-- The cell containing this site. -/
  cell : G
  /-- The label of this site within its cell. -/
  label : C.UnitCell

/-- A site is a pair of its unit-cell label and its cell. -/
def siteEquiv (C : Crystal G) : C.Site ≃ C.UnitCell × G where
  toFun x := (x.label, x.cell)
  invFun p := ⟨p.2, p.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Sites can be compared when cells and unit-cell labels can be compared. -/
instance (C : Crystal G) [DecidableEq G] [DecidableEq C.UnitCell] : DecidableEq C.Site :=
  (siteEquiv C).decidableEq

/-- A finite set of cells and a finite unit cell give a finite set of sites. -/
instance (C : Crystal G) [Fintype G] [Fintype C.UnitCell] : Fintype C.Site :=
  Fintype.ofEquiv _ (siteEquiv C).symm

/-- A finite translation group, as for periodic boundary conditions, gives a finite crystal. -/
instance (C : Crystal G) [Finite G] : Finite C.Site :=
  Finite.of_equiv _ (siteEquiv C).symm

/-- Every crystal has a site in its reference cell. -/
instance (C : Crystal G) : Nonempty C.Site :=
  let ⟨i⟩ := C.nonemptyUnitCell
  ⟨⟨0, i⟩⟩

/-! ## D. Translation symmetry -/

/-- Translate a site to another cell, preserving its unit-cell label. -/
instance (C : Crystal G) : AddAction G C.Site where
  vadd a x := ⟨a + x.cell, x.label⟩
  zero_vadd _ := Site.ext (zero_add _) rfl
  add_vadd _ _ _ := Site.ext (add_assoc _ _ _) rfl

/-- Translation changes a site's cell and preserves its label. -/
lemma Site.vadd_def {C : Crystal G} (a : G) (x : C.Site) :
    a +ᵥ x = ⟨a + x.cell, x.label⟩ := rfl

/-- The cell of a translated site is the translated cell. -/
@[simp] lemma Site.cell_vadd {C : Crystal G} (a : G) (x : C.Site) :
    (a +ᵥ x).cell = a + x.cell := rfl

/-- Translation preserves the label of a site. -/
@[simp] lemma Site.label_vadd {C : Crystal G} (a : G) (x : C.Site) :
    (a +ᵥ x).label = x.label := rfl

/-- Translation acts freely: translations are injective on sites, and different translations move
a site to different sites. -/
instance (C : Crystal G) : IsCancelVAdd G C.Site where
  toIsLeftCancelVAdd := inferInstance
  right_cancel' _ _ _ h := add_right_cancel (congrArg Site.cell h)

/-- The translates of a site are exactly the sites with the same label. -/
lemma Site.mem_orbit_iff_label_eq {C : Crystal G} (x y : C.Site) :
    y ∈ AddAction.orbit G x ↔ x.label = y.label := by
  rw [AddAction.mem_orbit_iff]
  constructor
  · rintro ⟨a, rfl⟩
    rfl
  · intro h
    exact ⟨y.cell - x.cell, Site.ext (by simp) (by simpa using h)⟩

end Crystal
end Physlib.CondensedMatter
