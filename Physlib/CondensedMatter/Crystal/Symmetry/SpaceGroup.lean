/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Algebra.Group.Action.Pointwise.Finset
public import Physlib.CondensedMatter.Crystal.PeriodicGraph
public import Physlib.CondensedMatter.Crystal.Symmetry.PointOperations

/-!
# Space group of a periodic graph

The crystal symmetries preserving the bonds of a periodic graph.

## i. Overview

The atoms of a real crystal are linked by bonds. Many symmetries of the bare lattice destroy these
links. A square lattice with bonds only along one axis loses the quarter turn. The symmetries
that keep every link in place form the space group of the bonded crystal. A symmetry belongs to it
when two sites are linked exactly if their images are linked,

`Adj (φ x) (φ y) ↔ Adj x y`.

A periodic graph is fixed by finitely many bonds of the reference cell. A symmetry therefore
belongs to the space group exactly when it permutes these bonds. The space group is the
stabilizer of the bond set.

Dropping the shifts of a space group leaves its point group. In a crystal embedded in space the
point group consists of rotations and reflections.

## ii. Key results

- `PeriodicGraph.spaceGroup`: The crystal symmetries permuting the bonds, the stabilizer of the
  bond set.
- `PeriodicGraph.mem_spaceGroup_iff`: A symmetry belongs to the space group exactly when it
  preserves adjacency.
- `PeriodicGraph.pointGroup`: The point operations of the space group.

## iii. Table of contents

- A. Space group and translations
- B. Point group

## iv. References

* F. Göhmann, *Introduction to Solid State Physics*, lecture L3, Section 3.1.
  [ref: goehmann_solid_state_2021]

-/

@[expose] public section

open Pointwise

namespace Physlib.CondensedMatter.Crystal

variable {G : Type*} [AddCommGroup G] [AddGroup.FG G] {C : Crystal G}

namespace PeriodicGraph

variable {g : PeriodicGraph C} {φ ψ : Symmetry C}

/-! ## A. Space group and translations -/

/-- A symmetry maps the sites linked by a bond to the sites linked by the image bond, so they are
adjacent exactly when the image bond is in the graph. -/
lemma adj_smul_iff {b : Bond C} {x y : C.Site} (h : b.Links x y) :
    g.toSimpleGraph.Adj (φ x) (φ y) ↔ φ • b ∈ g.bonds :=
  g.adj_iff_mem_bonds (φ.mapBond_links h)

/-- A symmetry that preserves adjacency maps a bond to a bond of the graph exactly when the bond is
one. -/
lemma smul_mem_bonds_iff_of_adj
    (h : ∀ x y, g.toSimpleGraph.Adj (φ x) (φ y) ↔ g.toSimpleGraph.Adj x y) (b : Bond C) :
    φ • b ∈ g.bonds ↔ b ∈ g.bonds := by
  rw [← adj_smul_iff b.links_reference, h, g.adj_iff_mem_bonds b.links_reference]

section BondSet

variable [DecidableEq G] [DecidableEq C.UnitCell]

/-- The subgroup of crystal symmetries that permute the bonds of the graph: the stabilizer of the
bond set. -/
noncomputable def spaceGroup (g : PeriodicGraph C) : Subgroup (Symmetry C) :=
  MulAction.stabilizer (Symmetry C) g.bonds

/-- A symmetry that permutes the bonds preserves adjacency. -/
lemma adj_iff_of_smul_eq (h : φ • g.bonds = g.bonds) (x y : C.Site) :
    g.toSimpleGraph.Adj (φ x) (φ y) ↔ g.toSimpleGraph.Adj x y := by
  have hl : (⟨x.label, y.label, y.cell - x.cell⟩ : Bond C).Links x y :=
    ⟨rfl, rfl, (add_sub_cancel _ _).symm⟩
  have hb := Finset.smul_mem_smul_finset_iff (s := g.bonds) φ (b := ⟨x.label, y.label,
    y.cell - x.cell⟩)
  rw [h] at hb
  rw [adj_smul_iff hl, g.adj_iff_mem_bonds hl]
  exact hb

/-- A symmetry that preserves adjacency permutes the bonds. -/
lemma smul_eq_of_adj (h : ∀ x y, g.toSimpleGraph.Adj (φ x) (φ y) ↔ g.toSimpleGraph.Adj x y) :
    φ • g.bonds = g.bonds := by
  refine Finset.ext fun b => ?_
  rw [← Finset.inv_smul_mem_iff]
  refine smul_mem_bonds_iff_of_adj (fun x y => ?_) b
  simpa using (h (φ⁻¹ x) (φ⁻¹ y)).symm

/-- A crystal symmetry belongs to the space group exactly when it preserves adjacency. -/
lemma mem_spaceGroup_iff :
    φ ∈ g.spaceGroup ↔ ∀ x y, g.toSimpleGraph.Adj (φ x) (φ y) ↔ g.toSimpleGraph.Adj x y :=
  ⟨adj_iff_of_smul_eq, smul_eq_of_adj⟩

/-- Every lattice translation belongs to the space group. -/
lemma translation_mem_spaceGroup (a : G) : Symmetry.translation C a ∈ g.spaceGroup :=
  mem_spaceGroup_iff.2 (g.adj_vadd a)

/-- The translation subgroup is contained in the space group. -/
lemma translations_le_spaceGroup : Symmetry.translations C ≤ g.spaceGroup := by
  rintro _ ⟨a, rfl⟩
  exact translation_mem_spaceGroup _

/-! ## B. Point group -/

/-- The image of the space group under the point-operation homomorphism. -/
noncomputable def pointGroup (g : PeriodicGraph C) : Subgroup (Symmetry C) :=
  g.spaceGroup.map (Symmetry.pointOp C)

/-- A symmetry is in the point group exactly when it is a point operation of a space-group
element. -/
lemma mem_pointGroup_iff :
    ψ ∈ g.pointGroup ↔ ∃ φ ∈ g.spaceGroup, Symmetry.pointOp C φ = ψ :=
  Subgroup.mem_map

end BondSet

end PeriodicGraph

end Physlib.CondensedMatter.Crystal
