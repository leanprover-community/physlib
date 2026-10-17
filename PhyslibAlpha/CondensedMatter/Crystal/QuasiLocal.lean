/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.CondensedMatter.Crystal.Symmetry
public import PhyslibAlpha.CondensedMatter.QuasiLocal.Symmetry

/-!

# The quasi-local algebra of an infinite crystal

The quasi-local algebra of a crystal carries an action of its cell symmetries, the translations
among them.

## i. Overview

The sites of a crystal are the sites `⟨n, i⟩` of the cells `n`, a countable set, infinite for the
translation group `ℤ^d`. If every site carries the same finite configuration space `Ω₀`, such as
the two states of a spin, the observables of a finite set of sites form a matrix algebra, and the
quasi-local algebra of the crystal is the direct limit over the finite regions.

The group `CellSymmetry G F` of the crystal acts on its sites, so it acts on the quasi-local
algebra by `*`-automorphisms. This group contains the translations as a normal subgroup, so the
translations act as a subgroup of the automorphisms. A symmetry `s` and a translation `t_a`
satisfy `s t_a s⁻¹ = t_{A a}` in the group, and the action respects this relation. Every bond
preserving symmetry of a periodic graph is among the cell symmetries.

## ii. Key results

- `crystalAlgebra` : the quasi-local algebra of a crystal.
- `cellSymmetryAction` : the action of the cell symmetries by `*`-automorphisms.
- `translationAction` : the action of the translations.
- `cellSymmetryAction_translation_conj` : a symmetry carries the translation by `a` to the
  translation by `A a`.

## iii. Table of contents

- A. The quasi-local algebra of a crystal
- B. The symmetries and the translations

## iv. References

* O. Bratteli & D. Robinson, Operator Algebras and Quantum Statistical Mechanics 2,
  Section 6.1.

-/

@[expose] public section

noncomputable section

namespace CondensedMatter.Crystal

open ProbabilisticTheory.QuasiLocal CondensedMatter.QuasiLocal

variable {G F : Type*} [AddCommGroup G] [DecidableEq (CellSite G F)]
variable (Ω₀ : Type*) [Fintype Ω₀] [DecidableEq Ω₀]

/-! ## A. The quasi-local algebra of a crystal -/

/-- **The quasi-local algebra of an infinite crystal** whose sites all carry the finite
configuration space `Ω₀`. -/
abbrev crystalAlgebra (G F : Type*) [DecidableEq (CellSite G F)] :=
  (uniformNet (S := CellSite G F) Ω₀).Quasilocal

/-! ## B. The symmetries and the translations -/

/-- **The cell symmetries of a crystal act on its quasi-local algebra** by `*`-automorphisms. -/
def cellSymmetryAction : CellSymmetry G F →* (crystalAlgebra Ω₀ G F ≃⋆ₐ[ℂ] crystalAlgebra Ω₀ G F) :=
  symAction

/-- The translations as cell symmetries. -/
def translationHom (G F : Type*) [AddCommGroup G] : Multiplicative G →* CellSymmetry G F where
  toFun a := CellSymmetry.translation (Multiplicative.toAdd a)
  map_one' := by
    ext <;> simp [CellSymmetry.translation]
  map_mul' a b := by
    rw [toAdd_mul]
    exact (CellSymmetry.translation_mul _ _).symm

/-- **The translations act on the quasi-local algebra** by `*`-automorphisms. -/
def translationAction : Multiplicative G →* (crystalAlgebra Ω₀ G F ≃⋆ₐ[ℂ] crystalAlgebra Ω₀ G F) :=
  (cellSymmetryAction Ω₀).comp (translationHom G F)

/-- **Covariance**: a cell symmetry carries the translation by `a` to the translation by `A a`. -/
lemma cellSymmetryAction_translation_conj (s : CellSymmetry G F) (a : G) :
    cellSymmetryAction Ω₀ s * cellSymmetryAction Ω₀ (CellSymmetry.translation a) *
        (cellSymmetryAction Ω₀ s)⁻¹ =
      cellSymmetryAction Ω₀ (CellSymmetry.translation (s.linear a)) := by
  rw [← map_mul, ← map_inv, ← map_mul, CellSymmetry.mul_translation_mul_inv]

end CondensedMatter.Crystal

end
