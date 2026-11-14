/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.CondensedMatter.Crystal.Symmetry.Decomposition

/-!
# Species-preserving crystal symmetries

The symmetries of a crystal that keep every atom on a site of its own species.

## i. Overview

A species assignment gives each label of the unit cell a species, for example a chemical
element. Graphene and hexagonal boron nitride share the honeycomb lattice with two sites per
cell. In graphene both sites carry carbon and the inversion through the centre of a bond
exchanges them. In boron nitride one site carries boron and the other nitrogen. The same
inversion would put boron where nitrogen was, so it is no longer a symmetry.

A symmetry acts on species assignments by relabelling. The symmetries preserving an assignment
`q` form its stabilizer. Only the permutation `σ` of the labels matters: a symmetry preserves `q`
exactly when `q ∘ σ = q`. Lattice automorphisms and shifts are unrestricted. A single species
allows every symmetry. Distinct species on all labels allow exactly the symmetries that fix
every label.

## ii. Key results

- `Crystal.Symmetry.speciesGroup` : the symmetries preserving a species assignment.
- `Crystal.Symmetry.mem_speciesGroup_iff` : a symmetry preserves `q` exactly when `q ∘ σ = q`.
- `Crystal.Symmetry.speciesGroup_eq_ker_of_injective` : distinct species allow exactly the
  symmetries that fix every label.

## iii. Table of contents

- A. The species group
- B. Uniform and distinct species

## iv. References

* None.

-/

@[expose] public section

namespace Physlib.CondensedMatter.Crystal

variable {G : Type*} [AddCommGroup G] [AddGroup.FG G]

namespace Symmetry

variable {C : Crystal G} {Q : Type*} {φ : Symmetry C}

/-! ## A. The species group -/

/-- A symmetry carries the species of each label to the image label: `(φ • q) (σ i) = q i`. -/
local instance : MulAction (Symmetry C) (Species C Q) := arrowAction

/-- The symmetries preserving the species assignment `q`. -/
def speciesGroup (q : Species C Q) : Subgroup (Symmetry C) :=
  MulAction.stabilizer (Symmetry C) q

/-- A symmetry preserves `q` exactly when its label permutation `σ` satisfies `q ∘ σ = q`. -/
lemma mem_speciesGroup_iff {q : Species C Q} : φ ∈ speciesGroup q ↔ q ∘ φ.labelPerm = q := by
  rw [← inv_mem_iff, speciesGroup, MulAction.mem_stabilizer_iff, funext_iff, funext_iff]
  change (∀ i, q (φ⁻¹⁻¹ • i) = q i) ↔ _
  rw [inv_inv]
  rfl

/-- A symmetry built from `A`, `σ` and `s` preserves `q` exactly when `q ∘ σ = q`. -/
lemma ofParts_mem_speciesGroup_iff {q : Species C Q} (A : G ≃+ G) (σ : Equiv.Perm C.UnitCell)
    (s : C.UnitCell → G) : ofParts C A σ s ∈ speciesGroup q ↔ q ∘ σ = q := by
  rw [mem_speciesGroup_iff, labelPerm_ofParts]

/-- Every lattice translation preserves every species assignment. -/
lemma translations_le_speciesGroup (q : Species C Q) : translations C ≤ speciesGroup q := by
  rintro _ ⟨a, rfl⟩
  exact mem_speciesGroup_iff.2 rfl

/-! ## B. Uniform and distinct species -/

/-- A single species allows every symmetry. -/
lemma speciesGroup_const (c : Q) : speciesGroup (C := C) (Function.const _ c) = ⊤ :=
  (Subgroup.eq_top_iff' _).2 (fun _ => mem_speciesGroup_iff.2 rfl)

/-- Distinct species on all labels allow exactly the symmetries that fix every label. -/
lemma speciesGroup_eq_ker_of_injective {q : Species C Q} (hq : Function.Injective q) :
    speciesGroup q = (MulAction.toPermHom (Symmetry C) C.UnitCell).ker := by
  ext φ
  rw [mem_speciesGroup_iff, MonoidHom.mem_ker]
  constructor
  · intro h
    exact Equiv.ext (fun i => hq (congrFun h i))
  · intro h
    change q ∘ MulAction.toPermHom (Symmetry C) C.UnitCell φ = q
    rw [h]
    rfl

end Symmetry

end Physlib.CondensedMatter.Crystal
