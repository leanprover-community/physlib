/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import Physlib.CondensedMatter.Crystal.Embedding

/-!
# Bravais lattices

A Bravais lattice with one site per cell, repeated by `d` independent translations, and its
embedding given by `d` primitive vectors.

## i. Overview

A Bravais lattice of dimension `d` is the crystal with translation group `ℤᵈ` and a unit cell with
a single site. Its embedding in a normed space `E` is fixed by the `d` primitive vectors, one for
each generator of `ℤᵈ`: the cell `n` goes to the integer combination of these vectors with
coefficients `n j`, and the single site sits at the origin of its cell. The different lattice types
differ only in these vectors, so the general facts are proved here once.

## ii. Key results

- `Crystal.bravais` : the crystal with translation group `ℤᵈ` and one site per cell.
- `Crystal.Embedding.ofVectors` : the embedding of `Crystal.bravais d` given by `d` primitive
  vectors.
- `Crystal.Embedding.position_ofVectors` : the position of a site is the integer combination of
  the primitive vectors given by its cell.
- `Crystal.Embedding.isSpaceFilling_ofVectors_iff` : the embedding is space filling exactly when the
  primitive vectors span the space.
- `Crystal.Embedding.position_ofVectors_injective` : linearly independent primitive vectors give
  distinct positions to distinct sites.
- `Crystal.Embedding.finrank_eq_of_ofVectors` : a space-filling embedding with linearly
  independent primitive vectors lives in a space of dimension `d`.

## iii. Table of contents

- A. The crystal
- B. The embedding
- C. Spanning and independence

## iv. References

* None.

-/

@[expose] public section

namespace Physlib.CondensedMatter.Crystal

/-! ## A. The crystal -/

/-- The Bravais lattice of dimension `d`: the translation group is `ℤᵈ` and the unit cell has a
single site. -/
abbrev bravais (d : ℕ) : Crystal (Fin d → ℤ) := Crystal.ofUnitCell (Fin d → ℤ) Unit

namespace Embedding

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E]

/-! ## B. The embedding -/

/-- The vector of the translation `n` is the integer combination of the primitive vectors with
coefficients `n j`. -/
def vectorHom (v : Fin d → E) : (Fin d → ℤ) →+ E where
  toFun n := ∑ j, n j • v j
  map_zero' := by simp
  map_add' n m := by simp [add_smul, Finset.sum_add_distrib]

/-- The embedding of the Bravais lattice of dimension `d` given by `d` primitive vectors. The
single site of a cell sits at the origin of the cell. -/
def ofVectors (v : Fin d → E) : Embedding (bravais d) E where
  vector := vectorHom v
  basis _ := 0

/-- The position of a site is the integer combination of the primitive vectors given by its
cell. -/
lemma position_ofVectors (v : Fin d → E) (x : (bravais d).Site) :
    (ofVectors v).position x = ∑ j, x.cell j • v j := by
  simp [position, ofVectors, vectorHom]

/-! ## C. Spanning and independence -/

variable [NormedSpace ℝ E]

/-- The embedding of a Bravais lattice is space filling exactly when the primitive vectors span
the space. -/
lemma isSpaceFilling_ofVectors_iff (v : Fin d → E) :
    (ofVectors v).IsSpaceFilling ↔ Submodule.span ℝ (Set.range v) = ⊤ := by
  have h : Submodule.span ℝ (Set.range (ofVectors v).vector) = Submodule.span ℝ (Set.range v) := by
    refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
    · rintro _ ⟨n, rfl⟩
      show ∑ j, n j • v j ∈ Submodule.span ℝ (Set.range v)
      refine Submodule.sum_mem _ fun j _ => ?_
      rw [← Int.cast_smul_eq_zsmul ℝ]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    · rintro _ ⟨j, rfl⟩
      refine Submodule.subset_span ⟨Pi.single j 1, ?_⟩
      simp [ofVectors, vectorHom, Pi.single_apply]
  rw [IsSpaceFilling, h]

/-- Linearly independent primitive vectors give distinct positions to distinct sites. -/
lemma position_ofVectors_injective {v : Fin d → E} (hv : LinearIndependent ℝ v) :
    Function.Injective (ofVectors v).position := by
  intro x y hxy
  rw [position_ofVectors, position_ofVectors] at hxy
  have hcell : x.cell = y.cell := by
    funext j
    apply Int.cast_injective (α := ℝ)
    apply hv.eq_coords_of_eq (f := (Int.cast : ℤ → ℝ) ∘ x.cell)
      (g := (Int.cast : ℤ → ℝ) ∘ y.cell)
    simpa only [Function.comp_apply, Int.cast_smul_eq_zsmul] using hxy
  exact Crystal.Site.ext hcell (Subsingleton.elim _ _)

/-- A space-filling embedding of a Bravais lattice with linearly independent primitive vectors
lives in a space of dimension `d`. -/
lemma finrank_eq_of_ofVectors {v : Fin d → E} (hv : LinearIndependent ℝ v)
    (h : (ofVectors v).IsSpaceFilling) : Module.finrank ℝ E = d := by
  have hspan : ⊤ ≤ Submodule.span ℝ (Set.range v) := ((isSpaceFilling_ofVectors_iff v).1 h).ge
  simpa using Module.finrank_eq_card_basis (Module.Basis.mk hv hspan)

end Embedding

end Physlib.CondensedMatter.Crystal
