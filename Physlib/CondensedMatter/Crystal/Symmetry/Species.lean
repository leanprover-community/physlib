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

/-- The crystal symmetries that preserve the species assignment `q`. -/
def speciesGroup (q : Species C Q) : Subgroup (Symmetry C) where
  carrier := {φ | ∀ i, q (φ • i) = q i}
  one_mem' := by
    intro i
    rfl
  mul_mem' {φ ψ} hφ hψ := by
    intro i
    rw [mul_smul, hφ, hψ]
  inv_mem' {φ} hφ := by
    intro i
    rw [← hφ (φ⁻¹ • i), smul_inv_smul]

/-- A symmetry preserves `q` exactly when it sends every label to one of the same species. -/
lemma mem_speciesGroup_iff {q : Species C Q} {φ : Symmetry C} :
    φ ∈ speciesGroup q ↔ ∀ i, q (φ • i) = q i := by
  rfl

/-- Every crystal symmetry preserves a constant species assignment. -/
lemma speciesGroup_const (c : Q) : speciesGroup (C := C) (Function.const _ c) = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro φ i
  rfl

/-- A symmetry that fixes every unit-cell label preserves any species assignment. -/
lemma ker_labelHom_le_speciesGroup (q : Species C Q) : (labelHom C).ker ≤ speciesGroup q := by
  intro φ hφ i
  exact congrArg q (Equiv.ext_iff.1 hφ i)

/-- With distinct species on distinct labels, preserving species requires fixing every label. -/
lemma speciesGroup_eq_ker_labelHom {q : Species C Q} (hq : Function.Injective q) :
    speciesGroup q = (labelHom C).ker := by
  refine le_antisymm ?_ (ker_labelHom_le_speciesGroup q)
  intro φ hφ
  ext i
  exact hq (hφ i)

/-! ## B. Merging species -/

/-- Applying `f` to the species values can only enlarge the species group. -/
lemma speciesGroup_le_comp (q : Species C Q) {Q' : Type*} (f : Q → Q') :
    speciesGroup q ≤ speciesGroup (f ∘ q) := by
  intro φ h i
  exact congrArg f (h i)

/-! ## C. Shifts and translations -/

/-- Every shift fixes the unit-cell labels and so preserves species. -/
lemma shift_mem_speciesGroup (q : Species C Q) (b : C.UnitCell → G) :
    shift C b ∈ speciesGroup q := by
  intro i
  rfl

/-- Every translation preserves any species assignment. -/
lemma translations_le_speciesGroup (q : Species C Q) : translations C ≤ speciesGroup q := by
  rintro _ ⟨a, rfl⟩ i
  rfl

end Symmetry

end Physlib.CondensedMatter.Crystal
