/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.CondensedMatter.Crystal.Basic
public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# A crystal in space

Embedding of a crystal into a space.

## i. Overview

Given a normed additive commutative group `E`, an embedding sends each translation of the crystal to
a vector in `E` and each site of the reference cell to a point in `E`. The site `(n, i)` is then
placed at the vector of `n` plus the point of `i`. The embedding is space filling if the vectors of
the translations span `E`.

## ii. Key results

- `Crystal.Embedding` : the vectors `ρ` of the translations and the positions `p` of the
  sites of the reference cell, in a normed group.
- `Crystal.Embedding.positionHom` : the positions commute with the translations, as an equivariant
  map of the sites.
- `Crystal.Embedding.position_vadd` : translating a site translates its position.
- `Crystal.Embedding.dist_position_vadd` : translating two sites does not change the
  distance between their positions.
- `Crystal.Embedding.IsSpaceFilling` : the vectors of the translations span the space.
- `Crystal.Embedding.isSpaceFilling_iff` : space filling can be checked on a generating set.
- `Crystal.Embedding.IsSpaceFilling.finiteDimensional` : a space-filling embedding lies in a
  finite-dimensional space.
- `Crystal.Embedding.IsSpaceFilling.finrank_eq_rank` : the dimension of the space equals the rank
  of the translation group when the vectors of a basis of the group are linearly independent.

## iii. Table of contents

- A. Vectors and positions
- B. Filling the space

## iv. References

* None.

-/

@[expose] public section

namespace Physlib.CondensedMatter.Crystal

variable {G : Type*} [AddCommGroup G] [AddGroup.FG G]

/-! ## A. Vectors and positions -/

/-- An embedding of a crystal in a normed group `E`. It assigns a vector to each translation and a
position to each site of the reference cell. -/
structure Embedding (C : Crystal G) (E : Type*) [NormedAddCommGroup E] where
  /-- The vector of a translation. -/
  vector : G →+ E
  /-- The position of the site with a given label in the reference cell. -/
  basis : C.UnitCell → E

namespace Embedding

variable {C : Crystal G} {E : Type*} [NormedAddCommGroup E] (R : Embedding C E)

/-- The site `(n, i)` sits at the vector of `n` plus the position of the label `i`. -/
def position (x : C.Site) : E := R.vector x.cell + R.basis x.label

/-- Translating a site by `a` translates its position by the vector of `a`. -/
lemma position_vadd (a : G) (x : C.Site) : R.position (a +ᵥ x) = R.vector a + R.position x := by
  simp [position, add_assoc]

/-- The translation group acts on the space by its vectors. -/
abbrev action : AddAction G E := AddAction.compHom E R.vector

/-- The positions commute with the translations. -/
def positionHom : letI := R.action; AddActionHom (id : G → G) C.Site E :=
  letI := R.action
  { toFun := R.position
    map_vadd' := R.position_vadd }

/-- Translating two sites does not change the distance between their positions. -/
lemma dist_position_vadd (a : G) (x y : C.Site) :
    Dist.dist (R.position (a +ᵥ x)) (R.position (a +ᵥ y)) =
      Dist.dist (R.position x) (R.position y) := by
  simp [position_vadd]

/-! ## B. Filling the space -/

variable [NormedSpace ℝ E]

/-- The embedding is space filling if the vectors of the translations span the space, so that the
crystal repeats in every direction. -/
def IsSpaceFilling : Prop := Submodule.span ℝ (Set.range R.vector) = ⊤

/-- An embedding fills the space exactly when the vectors of a generating set of the translation
group span it. -/
lemma isSpaceFilling_iff {S : Set G} (hS : AddSubgroup.closure S = ⊤) :
    R.IsSpaceFilling ↔ Submodule.span ℝ (R.vector '' S) = ⊤ := by
  have h : Submodule.span ℝ (Set.range R.vector) = Submodule.span ℝ (R.vector '' S) := by
    refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono (Set.image_subset_range _ _))
    rintro _ ⟨g, rfl⟩
    refine (AddSubgroup.closure_le
      ((Submodule.span ℝ (R.vector '' S)).toAddSubgroup.comap R.vector)).2 ?_
      (hS ▸ AddSubgroup.mem_top g)
    intro x hx
    exact Submodule.subset_span ⟨x, hx, rfl⟩
  rw [IsSpaceFilling, h]

/-- A space-filling embedding is in a finite-dimensional space. -/
lemma IsSpaceFilling.finiteDimensional (h : R.IsSpaceFilling) : FiniteDimensional ℝ E := by
  obtain ⟨S, hS, hfin⟩ := (AddSubgroup.fg_iff _).1 (AddGroup.fg_def.1 ‹AddGroup.FG G›)
  exact ⟨(R.isSpaceFilling_iff hS).1 h ▸ Submodule.fg_span (hfin.image _)⟩

/-- The dimension equals the rank of the translation group when the vectors of a basis of the
group are linearly independent over `ℝ`. -/
lemma IsSpaceFilling.finrank_eq_rank (h : R.IsSpaceFilling) {ι : Type*} [Fintype ι]
    (B : Module.Basis ι ℤ G) (hB : LinearIndependent ℝ (R.vector ∘ B)) :
    Module.finrank ℝ E = Module.finrank ℤ G := by
  have hS : AddSubgroup.closure (Set.range B) = ⊤ := by
    rw [← Submodule.span_int_eq_addSubgroupClosure, B.span_eq]
    rfl
  have hspan : ⊤ ≤ Submodule.span ℝ (Set.range (R.vector ∘ B)) := by
    rw [Set.range_comp]
    exact ((R.isSpaceFilling_iff hS).1 h).ge
  rw [Module.finrank_eq_card_basis B, Module.finrank_eq_card_basis (Module.Basis.mk hB hspan)]

end Embedding

end Physlib.CondensedMatter.Crystal
