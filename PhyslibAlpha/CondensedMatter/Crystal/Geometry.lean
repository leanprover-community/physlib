/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.CondensedMatter.Crystal.Graph
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!

# Crystal geometry

## i. Overview

The geometry of a crystal assigns a physical position to each site. Positions lie in a
metric space `A`, on which the translation group `G` acts by isometries. Translating a
site translates its position by the same group element. Distinct sites occupy distinct
positions.

The physical space may be Euclidean for an infinite crystal,
or a torus for a finite periodic crystal. Its translation action specifies the
physical displacement associated with each cell translation. The periodic and ambient
dimensions need not coincide: a sheet can be embedded in three-dimensional space.

`Geometry C A` supplies the embedding `position` of a crystal `C` into `A`. The physical
distance between sites is the distance between their positions. It is invariant under a
common translation and vanishes exactly when the sites coincide. The same distances
define a metric on the site set through `Geometry.metricSpace`.

## ii. Key results

- `Geometry` : an embedding of a crystal into a metric space compatible with translations.
- `Geometry.ofDisplacements` : positions from lattice displacements and unit-cell offsets.
- `latticeMap` : the linear map from cell indices to physical translations.
- `Geometry.distance_eq_of_adj` : bond lengths depend only on the bond.

## iii. Table of contents

- A. Positions and translations
- B. Physical distances
- C. Positions from a unit cell
- D. Bond lengths
- E. Euclidean lattice displacements

## iv. References

* N. Ashcroft & N. D. Mermin, Solid State Physics, Chapter 4.

-/

@[expose] public section

namespace CondensedMatter.Crystal

/-! ## A. Positions and translations -/

/-- An embedding of a crystal into physical space, compatible with translations. -/
structure Geometry {G : Type*} [AddGroup G] (C : Crystal G) (A : Type*)
    [MetricSpace A] where
  /-- Physical translations of the ambient space. -/
  [translations : AddAction G A]
  /-- Physical translations preserve ambient distances. -/
  [isometricTranslations : IsIsometricVAdd G A]
  /-- Physical positions, with distinct sites mapped to distinct points. -/
  position : C.Site ↪ A
  /-- A translated site occupies the corresponding translated position. -/
  position_vadd : ∀ (a : G) (x : C.Site), position (a +ᵥ x) = a +ᵥ position x

namespace Geometry

variable {G : Type*} [AddGroup G] {C : Crystal G} {A : Type*}
  [MetricSpace A]

/-! ## B. Physical distances -/

/-- Physical distance between two sites. -/
noncomputable def distance (R : Geometry C A) (x y : C.Site) : ℝ :=
  dist (R.position x) (R.position y)

/-- A common cell translation preserves the distance between sites. -/
@[simp] lemma distance_vadd (R : Geometry C A) (a : G) (x y : C.Site) :
    R.distance (a +ᵥ x) (a +ᵥ y) = R.distance x y := by
  let := R.translations
  let := R.isometricTranslations
  simp only [distance, R.position_vadd]
  exact (isometry_vadd A a).dist_eq _ _

/-- Zero physical distance identifies the same site. -/
@[simp] lemma distance_eq_zero (R : Geometry C A) (x y : C.Site) :
    R.distance x y = 0 ↔ x = y := by
  rw [distance, dist_eq_zero, R.position.injective.eq_iff]

/-- The metric on crystal sites inherited from their physical positions. -/
@[instance_reducible]
noncomputable def metricSpace (R : Geometry C A) : MetricSpace C.Site :=
  MetricSpace.induced R.position R.position.injective inferInstance

/-- The position embedding preserves the induced physical metric. -/
lemma isometry_position (R : Geometry C A) :
    letI := R.metricSpace
    Isometry R.position := by
  intro x y
  rfl

/-! ## C. Positions from a unit cell

Specify the positions of the sites in the reference cell. The position of site `i` in
cell `n` is the translate `n +ᵥ basisPositions i`. These positions must distinguish all
sites, including copies in different cells.
-/

/-- Embed a repeated unit cell by translating its reference positions.
The injectivity condition ensures that no two site addresses occupy the same point. -/
def ofUnitCell (G F : Type*) [AddGroup G] [Finite F] (A : Type*)
    [MetricSpace A] [AddAction G A] [IsIsometricVAdd G A]
    (basisPositions : F → A)
    (injective : Function.Injective (fun x : CellSite G F => x.cell +ᵥ basisPositions x.label)) :
    Geometry (Crystal.ofUnitCell G F) A where
  translations := inferInstance
  isometricTranslations := inferInstance
  position := ⟨fun x => x.cell +ᵥ basisPositions x.label, injective⟩
  position_vadd a x := by
    change (a + x.cell) +ᵥ basisPositions x.label = a +ᵥ (x.cell +ᵥ basisPositions x.label)
    exact add_vadd _ _ _

/-- Embed a unit cell using physical displacements and reference positions.
The translation map specifies the displacement of each cell; the injectivity condition
ensures that different sites have different physical positions. -/
def ofDisplacements {G F A : Type*} [AddGroup G] [Finite F] [NormedAddCommGroup A]
    (displacement : G →+ A) (basisPositions : F → A)
    (injective : Function.Injective
      (fun x : CellSite G F => displacement x.cell + basisPositions x.label)) :
    Geometry (Crystal.ofUnitCell G F) A := by
  letI := AddAction.compHom A displacement
  letI : IsIsometricVAdd G A := ⟨fun a => isometry_add_left (displacement a)⟩
  exact ofUnitCell G F A basisPositions injective

/-- A site's position is its cell displacement plus its position within the reference cell. -/
@[simp] lemma position_ofDisplacements {G F A : Type*} [AddGroup G] [Finite F]
    [NormedAddCommGroup A] (displacement : G →+ A) (basisPositions : F → A)
    (injective : Function.Injective
      (fun x : CellSite G F => displacement x.cell + basisPositions x.label))
    (x : CellSite G F) :
    (ofDisplacements displacement basisPositions injective).position x =
      displacement x.cell + basisPositions x.label := rfl

/-- A one-site unit cell embedded by an injective physical translation map. -/
def ofLattice {G A : Type*} [AddGroup G] [NormedAddCommGroup A]
    (displacement : G →+ A) (injective : Function.Injective displacement) :
    Geometry (Crystal.ofUnitCell G Unit) A :=
  ofDisplacements displacement (fun _ => 0) (by
    intro x y h
    apply CellSite.ext
    · exact injective (by simpa only [add_zero] using h)
    · exact Subsingleton.elim _ _)

/-- In a one-site cell, the site's position is its cell displacement. -/
@[simp] lemma position_ofLattice {G A : Type*} [AddGroup G] [NormedAddCommGroup A]
    (displacement : G →+ A) (injective : Function.Injective displacement)
    (x : CellSite G Unit) : (ofLattice displacement injective).position x =
      displacement x.cell := by
  change displacement x.cell + 0 = displacement x.cell
  exact add_zero _

/-! ## D. Bond lengths

Translations preserve bond lengths. It therefore suffices to check the bonds starting
in the reference cell to determine the lengths of all graph edges.
-/

/-- Every translated copy of a bond has its reference-cell length. -/
lemma distance_of_links {G F A : Type*} [AddGroup G] [Finite F] [MetricSpace A]
    (R : Geometry (Crystal.ofUnitCell G F) A) (b : Bond G F)
    {x y : CellSite G F} (h : b.Links x y) :
    R.distance x y = R.distance ⟨0, b.source⟩ ⟨b.displacement, b.target⟩ := by
  rcases x with ⟨n, i⟩
  rcases y with ⟨m, j⟩
  rcases h with ⟨rfl, rfl, rfl⟩
  have h := R.distance_vadd n ⟨0, b.source⟩ ⟨b.displacement, b.target⟩
  change R.distance ⟨n + 0, b.source⟩ ⟨n + b.displacement, b.target⟩ = _ at h
  simpa only [add_zero] using h

/-- A common reference bond length gives the length of every generated graph edge. -/
lemma distance_eq_of_adj {G F A : Type*} [AddGroup G] [Finite F] [MetricSpace A]
    (R : Geometry (Crystal.ofUnitCell G F) A) (bonds : List (Bond G F)) (length : ℝ)
    (h : ∀ b ∈ bonds, R.distance ⟨0, b.source⟩ ⟨b.displacement, b.target⟩ = length)
    {x y : CellSite G F} (hxy : (graphFromBonds bonds).Adj x y) : R.distance x y = length := by
  obtain ⟨_, b, hb, hxy | hyx⟩ := hxy
  · exact (R.distance_of_links b hxy).trans (h b hb)
  · change dist (R.position x) (R.position y) = length
    rw [dist_comm]
    exact (R.distance_of_links b hyx).trans (h b hb)

end Geometry

/-! ## E. Euclidean lattice displacements

Primitive vectors specify the physical displacement of an integer cell index. Their
linear independence ensures that distinct cells have distinct displacements.
-/

/-- Convert integer cell coordinates into physical displacements along primitive vectors. -/
noncomputable def latticeMap {d D : ℕ} (vectors : Fin d → EuclideanSpace ℝ (Fin D)) :
    (Fin d → ℤ) →+ EuclideanSpace ℝ (Fin D) where
  toFun n := ∑ j, (n j : ℝ) • vectors j
  map_zero' := by simp
  map_add' n m := by simp [Int.cast_add, add_smul, Finset.sum_add_distrib]

/-- Independent primitive vectors separate the displacements of different cells. -/
lemma latticeMap_injective {d D : ℕ} {vectors : Fin d → EuclideanSpace ℝ (Fin D)}
    (independent : LinearIndependent ℝ vectors) : Function.Injective (latticeMap vectors) := by
  intro n m h
  have hz : ∑ j, ((n - m) j : ℝ) • vectors j = 0 := by
    change latticeMap vectors (n - m) = 0
    rw [map_sub, h, sub_self]
  have hc := Fintype.linearIndependent_iff.mp independent _ hz
  funext j
  have hj : n j - m j = 0 := by exact_mod_cast hc j
  exact sub_eq_zero.mp hj

end CondensedMatter.Crystal
