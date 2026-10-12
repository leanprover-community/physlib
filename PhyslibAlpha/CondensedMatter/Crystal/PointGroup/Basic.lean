/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.CondensedMatter.Crystal.Symmetry
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Algebra.Group.End

/-!

# Point groups of Bravais lattices

The point group of a crystal with one site per cell is the group of automorphisms of its
translation lattice that preserve its bonds.

## i. Overview

The point group of a crystal is the group of its bond-preserving symmetries modulo translations.
A symmetry of any crystal acts on the lattice of cell translations by a lattice automorphism, its
linear part, and this gives a homomorphism `pointLinearHom` from the point group to the lattice
automorphisms. It is not injective in general: a symmetry may permute the sites within every cell
and move none of the cells, and such a symmetry is not a translation.

When there is one site per cell, a symmetry is determined, up to a translation, by its linear part.
An automorphism of the lattice then extends to a bond-preserving symmetry exactly when it maps
the set of bonded displacements to itself. In this case the point group is isomorphic to the
group of lattice automorphisms preserving the bonded displacements (`pointGroupEquiv`). This group
is finite when the graph is connected and has finitely many neighbours; it is the group of
rotations and reflections of the lattice that leave it invariant. No geometry is involved: a
square and a rectangular lattice with the same bonds have the same point group as graphs.

## ii. Key results

- `PeriodicGraph.pointLinearHom` : the action of the point group of any crystal on the lattice.
- `PeriodicGraph.pointStabilizer` : the lattice automorphisms preserving the bonded displacements.
- `PeriodicGraph.pointGroupEquiv` : the point group is isomorphic to this group.

## iii. Table of contents

- A. Automorphisms preserving the bonds
- B. The point group of a crystal with one site per cell
- C. The action on the lattice of any crystal

## iv. References

* N. Ashcroft & N. D. Mermin, Solid State Physics, Chapter 7.

-/

@[expose] public section

namespace CondensedMatter.Crystal

namespace PeriodicGraph

variable {G : Type*} [AddCommGroup G]

/-! ## A. Automorphisms preserving the bonds -/

/-- The lattice automorphisms that map bonded displacements to bonded displacements. -/
def pointStabilizer (g : PeriodicGraph (Crystal.ofUnitCell G Unit)) :
    Subgroup (Multiplicative (AddAut G)) where
  carrier := {A | ∀ d, g.Bonded () () ((Multiplicative.toAdd A : AddAut G) d) ↔
    g.Bonded () () d}
  one_mem' d := Iff.rfl
  mul_mem' {A B} hA hB d := by
    change g.Bonded () () ((Multiplicative.toAdd A : AddAut G)
      ((Multiplicative.toAdd B : AddAut G) d)) ↔ _
    rw [hA, hB]
  inv_mem' {A} hA d := by
    have h := hA ((Multiplicative.toAdd A⁻¹ : AddAut G) d)
    have e : (Multiplicative.toAdd A : AddAut G) ((Multiplicative.toAdd A⁻¹ : AddAut G) d) = d :=
      AddEquiv.apply_symm_apply _ d
    rw [e] at h
    exact h.symm

/-- The linear part of a cell symmetry as a homomorphism to the lattice automorphisms. -/
def linearHom (G F : Type*) [AddCommGroup G] : CellSymmetry G F →* Multiplicative (AddAut G) where
  toFun s := Multiplicative.ofAdd s.linear
  map_one' := rfl
  map_mul' _s _t := rfl

/-- Bond-preserving symmetries have linear parts in the point stabilizer. -/
lemma linear_mem_pointStabilizer (g : PeriodicGraph (Crystal.ofUnitCell G Unit))
    {s : CellSymmetry G Unit} (hs : s ∈ g.symmetries) :
    Multiplicative.ofAdd s.linear ∈ g.pointStabilizer := by
  intro d
  have := (mem_symmetries_iff g s).1 hs () () d
  simp only [add_sub_cancel_right] at this
  exact this.symm

/-! ## B. The point group of a crystal with one site per cell -/

/-- The homomorphism from bond-preserving symmetries to the point stabilizer taking a symmetry to
its action on the lattice. -/
def pointHom (g : PeriodicGraph (Crystal.ofUnitCell G Unit)) :
    g.symmetries →* g.pointStabilizer :=
  ((linearHom G Unit).comp g.symmetries.subtype).codRestrict g.pointStabilizer
    fun s => linear_mem_pointStabilizer g s.2

lemma pointHom_surjective (g : PeriodicGraph (Crystal.ofUnitCell G Unit)) :
    Function.Surjective (pointHom g) := by
  rintro ⟨A, hA⟩
  refine ⟨⟨⟨Multiplicative.toAdd A, 1, fun _ => 0⟩, ?_⟩, rfl⟩
  rw [mem_symmetries_iff]
  rintro ⟨⟩ ⟨⟩ d
  simpa using (hA d).symm

lemma ker_pointHom (g : PeriodicGraph (Crystal.ofUnitCell G Unit)) :
    (pointHom g).ker = (CellSymmetry.translations G Unit).subgroupOf g.symmetries := by
  ext s
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro h
    have hl : Multiplicative.ofAdd (s : CellSymmetry G Unit).linear = 1 := congrArg Subtype.val h
    refine ⟨(s : CellSymmetry G Unit).shift (), ?_⟩
    refine CellSymmetry.ext ?_ ?_ ?_
    · exact AddEquiv.ext fun x =>
        congrArg (fun f : Multiplicative (AddAut G) => (Multiplicative.toAdd f : AddAut G) x) hl
    · exact Subsingleton.elim _ _
    · exact funext fun u => by cases u; rfl
  · rintro ⟨a, ha⟩
    refine Subtype.ext ?_
    change Multiplicative.ofAdd (s : CellSymmetry G Unit).linear = 1
    rw [ha]
    rfl

/-- **The point group of a crystal with one site per cell is the group of lattice automorphisms
preserving the bonded displacements.** -/
noncomputable def pointGroupEquiv (g : PeriodicGraph (Crystal.ofUnitCell G Unit)) :
    g.pointGroup ≃* g.pointStabilizer :=
  (QuotientGroup.quotientMulEquivOfEq (ker_pointHom g).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (pointHom_surjective g))

/-! ## C. The action on the lattice of any crystal -/

/-- **The point group of any crystal acts on its translation lattice** through the linear parts of
its symmetries. -/
noncomputable def pointLinearHom {F : Type*} [Finite F]
    (g : PeriodicGraph (Crystal.ofUnitCell G F)) : g.pointGroup →* Multiplicative (AddAut G) :=
  QuotientGroup.lift _ ((linearHom G F).comp g.symmetries.subtype) (by
    rintro ⟨s, hs⟩ ⟨a, rfl⟩
    rfl)

end PeriodicGraph

end CondensedMatter.Crystal
