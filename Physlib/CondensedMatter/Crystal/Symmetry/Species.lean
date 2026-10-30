/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.CondensedMatter.Crystal.Symmetry.PointOperations

/-!
# Species-preserving crystal symmetries

The crystal symmetries that preserve a species assignment.

## i. Overview

A species assignment gives each label of the unit cell a species, for example a chemical element.
The same assignment holds in every cell. A symmetry permutes the labels. It preserves an
assignment `q` when `q (φ • i) = q i` for every label `i`. These symmetries form `speciesGroup q`.

A constant assignment admits every symmetry. Distinct species on distinct labels admit exactly the
symmetries that fix every label. Merging species enlarges the group. Shifts and translations fix
every label. They preserve every assignment.

## ii. Key results

- `Symmetry.speciesGroup` : the symmetries preserving a species assignment.
- `Symmetry.speciesGroup_const` : a constant assignment admits every symmetry.
- `Symmetry.speciesGroup_eq_ker_labelHom` : an injective assignment admits exactly the symmetries
  that fix every label.
- `Symmetry.speciesGroup_le_comp` : merging species cannot remove symmetries.
- `Symmetry.shift_mem_speciesGroup` : shifts preserve every assignment.
- `Symmetry.translations_le_speciesGroup` : translations preserve every assignment.

## iii. Table of contents

- A. Species-preserving symmetries
- B. Merging species
- C. Shifts and translations

## iv. References

* None.

-/

@[expose] public section

namespace Physlib.CondensedMatter.Crystal

variable {G : Type*} [AddCommGroup G] [AddGroup.FG G]

namespace Symmetry

variable {C : Crystal G} {Q : Type*}

/-! ## A. Species-preserving symmetries -/

/-- The crystal symmetries act on the species assignments through their action on the labels. -/
noncomputable instance : MulAction (Symmetry C) (Species C Q) := arrowAction

/-- The crystal symmetries that preserve the species assignment `q`. -/
noncomputable def speciesGroup (q : Species C Q) : Subgroup (Symmetry C) :=
  MulAction.stabilizer (Symmetry C) q

/-- A symmetry preserves `q` exactly when it sends every label to one of the same species. -/
lemma mem_speciesGroup_iff {q : Species C Q} {φ : Symmetry C} :
    φ ∈ speciesGroup q ↔ ∀ i, q (φ • i) = q i := by
  rw [← inv_mem_iff, speciesGroup, MulAction.mem_stabilizer_iff, funext_iff]
  show (∀ i, q ((φ⁻¹)⁻¹ • i) = q i) ↔ _
  rw [inv_inv]

/-- Every crystal symmetry preserves a constant species assignment. -/
lemma speciesGroup_const (c : Q) : speciesGroup (C := C) (Function.const _ c) = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro φ
  exact mem_speciesGroup_iff.2 (congrFun rfl)

/-- A symmetry that fixes every unit-cell label preserves any species assignment. -/
lemma ker_labelHom_le_speciesGroup (q : Species C Q) : (labelHom C).ker ≤ speciesGroup q := by
  intro φ hφ
  rw [mem_speciesGroup_iff]
  intro i
  exact congrArg q (Equiv.ext_iff.1 hφ i)

/-- With distinct species on distinct labels, preserving species requires fixing every label. -/
lemma speciesGroup_eq_ker_labelHom {q : Species C Q} (hq : Function.Injective q) :
    speciesGroup q = (labelHom C).ker := by
  refine le_antisymm ?_ (ker_labelHom_le_speciesGroup q)
  intro φ hφ
  ext i
  exact hq (mem_speciesGroup_iff.1 hφ i)

/-! ## B. Merging species -/

/-- Applying `f` to the species values can only enlarge the species group. -/
lemma speciesGroup_le_comp (q : Species C Q) {Q' : Type*} (f : Q → Q') :
    speciesGroup q ≤ speciesGroup (f ∘ q) := by
  intro φ h
  rw [mem_speciesGroup_iff] at h ⊢
  intro i
  exact congrArg f (h i)

/-! ## C. Shifts and translations -/

/-- Every shift fixes the unit-cell labels and so preserves species. -/
lemma shift_mem_speciesGroup (q : Species C Q) (b : C.UnitCell → G) :
    shift C b ∈ speciesGroup q :=
  mem_speciesGroup_iff.2 (congrFun rfl)

/-- Every translation preserves any species assignment. -/
lemma translations_le_speciesGroup (q : Species C Q) : translations C ≤ speciesGroup q := by
  rintro _ ⟨a, rfl⟩
  exact mem_speciesGroup_iff.2 (congrFun rfl)

end Symmetry

end Physlib.CondensedMatter.Crystal
