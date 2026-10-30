/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.CondensedMatter.Crystal.Embedding
public import Physlib.CondensedMatter.Crystal.Symmetry.PointOperations

/-!
# Isometries of an embedded crystal

An embedding assigns a position to each crystal site. This file studies the crystal symmetries
that preserve distances between those positions.

## i. Overview

A symmetry `φ` is an isometry of the embedded crystal when, for every pair of sites `x` and `y`,

`dist (R.position (φ x)) (R.position (φ y)) = dist (R.position x) (R.position y)`.

These symmetries form a subgroup. Every translation belongs to it because translating both
sites leaves their distance unchanged.

Every site is a lattice translate of a site in the reference cell, and translating both sites
leaves their distance unchanged. Consequently it suffices to check the condition on pairs in
which one site lies in the reference cell: a symmetry is an isometry exactly when it preserves the
distance from every site to every site of the reference cell.

## ii. Key results

- `Embedding.isometries`: crystal symmetries that preserve distances between site positions.
- `Embedding.translations_le_isometries`: every translation is an isometry.
- `Embedding.mem_isometries_iff_reference`: it suffices to check distances to the sites of the
  reference cell.

## iii. Table of contents

- A. Distance-preserving symmetries
- B. Distances to the reference cell

## iv. References

* None.

-/

@[expose] public section

namespace Physlib.CondensedMatter.Crystal

variable {G : Type*} [AddCommGroup G] [AddGroup.FG G]

namespace Embedding

variable {C : Crystal G} {E : Type*} [NormedAddCommGroup E] (R : Embedding C E) {φ : Symmetry C}

/-! ## A. Distance-preserving symmetries -/

/-- The crystal symmetries that preserve distances between all pairs of site positions. -/
def isometries : Subgroup (Symmetry C) where
  carrier := {φ | ∀ x y, dist (R.position (φ x)) (R.position (φ y)) =
    dist (R.position x) (R.position y)}
  one_mem' := by
    intro x y
    rfl
  mul_mem' {φ ψ} hφ hψ := by
    intro x y
    rw [Symmetry.mul_apply, Symmetry.mul_apply, hφ, hψ]
  inv_mem' {φ} hφ := by
    intro x y
    simpa using (hφ (φ⁻¹ x) (φ⁻¹ y)).symm

/-- A symmetry is an isometry exactly when it preserves every distance between site positions. -/
lemma mem_isometries_iff : φ ∈ R.isometries ↔
    ∀ x y, dist (R.position (φ x)) (R.position (φ y)) = dist (R.position x) (R.position y) := by
  rfl

/-- Translating both sites by the same lattice vector preserves their distance. -/
lemma translations_le_isometries : Symmetry.translations C ≤ R.isometries := by
  rintro _ ⟨a, rfl⟩ x y
  exact R.dist_position_vadd _ x y

/-! ## B. Distances to the reference cell -/

/-- A site is the lattice translate of the site with the same label in the reference cell. -/
lemma site_eq_vadd (x : C.Site) : x = x.cell +ᵥ (Site.ref x.label) :=
  Site.ext (by simp) rfl

/-- A symmetry is an isometry exactly when it preserves the distance from every site `(d, i)` to
every site `(0, j)` of the reference cell. -/
lemma mem_isometries_iff_reference : φ ∈ R.isometries ↔ ∀ (i j : C.UnitCell) (d : G),
    dist (R.position (φ ⟨d, i⟩)) (R.position (φ (Site.ref j))) =
      dist (R.position ⟨d, i⟩) (R.position (Site.ref j)) := by
  constructor
  · intro h i j d
    exact h _ _
  · intro h ⟨n, i⟩ ⟨m, j⟩
    have hx : (⟨n, i⟩ : C.Site) = m +ᵥ ⟨n - m, i⟩ := Site.ext (by simp) rfl
    rw [hx, site_eq_vadd ⟨m, j⟩, Symmetry.map_vadd, Symmetry.map_vadd, R.dist_position_vadd,
      R.dist_position_vadd]
    exact h _ _ _

end Embedding

end Physlib.CondensedMatter.Crystal
