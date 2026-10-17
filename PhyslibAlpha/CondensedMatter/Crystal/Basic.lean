/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.ZMod.Defs
public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.Tactic.DeriveFintype

/-!

# Crystals, cells and sites

## i. Overview

A crystal is a perfect periodic arrangement obtained by repeating a unit cell. The unit
cell contains finitely many sites, which may carry atoms, spins or orbitals. A cell is one
translated copy of the unit cell. A label identifies which site within that copy: for
example, A or B in a cell containing two sites. A cell index and a site label together
identify one site in the full crystal.

The translation group `G` determines how the cells repeat. The usual choice is `ℤᵈ`, giving
an infinite discrete crystal. Choosing `(ℤ/mℤ)ᵈ` with positive `m` gives a finite periodic
array with opposite boundaries identified. The definition also permits `ℝᵈ`, describing
continuously translated arrangements.

`Crystal.ofUnitCell G F` constructs the crystal from its translation group `G` and the
finite set `F` of site labels in the unit cell. Taking `F = Fin 2` gives two sites per cell,
labelled `0` and `1`. With `G = Fin 2 → ℤ`, the cells form an infinite two-dimensional
array. With `G = Fin 2 → ZMod 4`, there are four cells in each direction with periodic
identification.

For a crystal `C` built this way, `C.Site` is the type of its sites. The site `⟨n, i⟩` has
cell index `n` and label `i`. Translation by `a`, written `a +ᵥ x`, changes its cell index
to `a + n` and preserves its label. These indices specify site addresses; a geometric
realization supplies physical positions.

## ii. Key results

- `Crystal` : a perfectly repeating arrangement of sites under a translation group.
- `Crystal.ofUnitCell` : the crystal obtained by repeating a unit cell with finitely many labels.
- `CellSite` : the address of a site, a cell index together with a label.

## iii. Table of contents

- A. Constructing a crystal from a unit cell

## iv. References

* N. Ashcroft & N. D. Mermin, Solid State Physics, Chapter 4.

-/

@[expose] public section

namespace CondensedMatter

universe u v

/-- A perfectly repeating arrangement of sites under the translation group `G`.
Every site belongs to one of finitely many families of translated copies. -/
structure Crystal (G : Type u) [AddGroup G] where
  /-- The sites of the crystal. -/
  Site : Type v
  /-- Translation by `a : G` takes each site to its corresponding translated copy. -/
  [translations : AddAction G Site]
  /-- Different translations of a site give different sites. -/
  [free : IsCancelVAdd G Site]
  /-- A unit cell requires only finitely many site labels. -/
  [finiteSiteOrbits : Finite (AddAction.orbitRel.Quotient G Site)]

attribute [instance] Crystal.translations Crystal.free Crystal.finiteSiteOrbits

namespace Crystal

/-! ## A. Constructing a crystal from a unit cell

Choose site labels `F` for a reference cell. Repeating this cell under translations by `G`
gives one site for each cell index `n : G` and label `i : F`.
-/

/-- The address `⟨n, i⟩` of site `i` in the cell indexed by `n`. -/
@[ext] structure CellSite (G : Type u) (F : Type v) where
  /-- Translation from the reference cell to this cell. -/
  cell : G
  /-- Which site of the unit cell is being copied. -/
  label : F
  deriving DecidableEq, Fintype

/-- Translate a site by changing its cell index and preserving its label. -/
instance {G F : Type*} [AddGroup G] : AddAction G (CellSite G F) where
  vadd a x := ⟨a + x.cell, x.label⟩
  zero_vadd x := by change CellSite.mk (0 + x.cell) x.label = x; simp
  add_vadd a b x := by
    change CellSite.mk ((a + b) + x.cell) x.label = CellSite.mk (a + (b + x.cell)) x.label
    rw [add_assoc]

/-- Different cell translations give different copies of a site. -/
instance {G F : Type*} [AddGroup G] : IsCancelVAdd G (CellSite G F) where
  toIsLeftCancelVAdd := inferInstance
  right_cancel' _ _ _ h := add_right_cancel (congrArg CellSite.cell h)

/-- Construct a crystal by repeating a unit cell containing one site for each label in `F`.
The group `G` indexes translated cells. A site of the resulting crystal has address
`⟨n, i⟩`, where `n : G` specifies its cell and `i : F` identifies the site within that cell. -/
@[reducible]
def ofUnitCell (G : Type u) (F : Type v) [AddGroup G] [Finite F] : Crystal G where
  Site := CellSite G F
  translations := inferInstance
  free := inferInstance
  finiteSiteOrbits := by
    apply Finite.of_surjective (fun i : F =>
      Quotient.mk _ (⟨0, i⟩ : CellSite G F))
    intro q
    induction q using Quotient.inductionOn with
    | _ x =>
      refine ⟨x.label, Quotient.sound ?_⟩
      change AddAction.orbitRel G (CellSite G F) ⟨0, x.label⟩ x
      rw [AddAction.orbitRel_apply, AddAction.mem_orbit_iff]
      refine ⟨-x.cell, ?_⟩
      rcases x with ⟨n, i⟩
      change CellSite.mk (-n + n) i = CellSite.mk 0 i
      simp

/-- A finite translation group gives a finite crystal. -/
instance {G : Type*} [AddGroup G] [Finite G] (C : Crystal G) : Finite C.Site :=
  Finite.of_finite_addAction_orbitRel_quotient G C.Site

end Crystal
end CondensedMatter
