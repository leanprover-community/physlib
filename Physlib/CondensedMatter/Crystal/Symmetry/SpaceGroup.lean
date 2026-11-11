/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

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

- `PeriodicGraph.spaceGroup`: The crystal symmetries preserving adjacency.
- `PeriodicGraph.pointGroup`: The point operations of the space group.
- `PeriodicGraph.mem_spaceGroup_iff_preservesBonds`: A crystal symmetry belongs to the space
  group exactly when it preserves the finite bond set.
- `PeriodicGraph.spaceGroup_eq_stabilizer`: The space group is the stabilizer of the bond set.

## iii. Table of contents

- A. Space group and translations
- B. Point group
- C. The bond set

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

/-- The subgroup of crystal symmetries preserving adjacency. -/
noncomputable def spaceGroup (g : PeriodicGraph C) : Subgroup (Symmetry C) :=
  g.graphAutomorphisms.comap (Symmetry.toPerm C)

/-- A crystal symmetry belongs to the space group exactly when it preserves adjacency. -/
lemma mem_spaceGroup_iff :
    φ ∈ g.spaceGroup ↔ ∀ x y, g.toSimpleGraph.Adj (φ x) (φ y) ↔ g.toSimpleGraph.Adj x y := by
  rfl

/-- Every lattice translation belongs to the space group. -/
lemma translation_mem_spaceGroup (a : G) : Symmetry.translation C a ∈ g.spaceGroup := by
  intro x y
  exact g.adj_vadd a x y

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

/-! ## C. The bond set -/

section BondSet

variable [DecidableEq G] [DecidableEq C.UnitCell] [Fintype C.UnitCell]

/-- Every space-group symmetry preserves the reference-cell bonds. -/
lemma PreservesBonds.of_mem_spaceGroup (hφ : φ ∈ g.spaceGroup) : g.PreservesBonds φ := by
  intro b hb
  have hl := b.links_reference
  have hadj := (g.mem_bonds b).1 hb
  have hmap := (hφ _ _).2 hadj
  exact (g.adj_iff_mem_bonds (φ.mapBond_links hl)).1 hmap

/-- A crystal symmetry preserves adjacency exactly when it preserves the reference-cell bonds. -/
lemma mem_spaceGroup_iff_preservesBonds : φ ∈ g.spaceGroup ↔ g.PreservesBonds φ := by
  constructor
  · exact PreservesBonds.of_mem_spaceGroup
  · intro h
    rw [mem_spaceGroup_iff]
    intro x y
    constructor
    · intro hxy
      simpa using h.inv.map_adj hxy
    · exact h.map_adj

/-- The space group is the stabilizer of the set of reference-cell bonds. -/
lemma spaceGroup_eq_stabilizer :
    g.spaceGroup = MulAction.stabilizer (Symmetry C) g.bonds := by
  ext φ
  rw [mem_spaceGroup_iff_preservesBonds, preservesBonds_iff_smul_eq, MulAction.mem_stabilizer_iff]

end BondSet

end PeriodicGraph

end Physlib.CondensedMatter.Crystal
