/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.CondensedMatter.Crystal.Symmetries
public import Mathlib.GroupTheory.SemidirectProduct

/-!
# Shifts and point operations of a crystal

Every symmetry of a crystal is a shift of its sites followed by a point operation.

## i. Overview

Every symmetry of a crystal is of the form

`⟨n, i⟩ ↦ ⟨A n + c (σ i), σ i⟩`

for a lattice automorphism `A`, a permutation `σ` of the labels, and a shift `c j` of the sites
with label `j` by a lattice vector. Conversely, every choice of `A`, `σ` and `c` gives a symmetry.
A translation is the case where `A` and `σ` do nothing and `c` is the same vector for every label.
The shifts form a normal subgroup, and the pairs `(A, σ)`, the point operations, act on it by
`c ↦ A ∘ c ∘ σ⁻¹`. Hence the symmetry group is the semidirect product of the shifts and the point
operations. Sending a symmetry to its point operation is a homomorphism whose kernel is the shifts.
The linear part is the first component of the point operation. For a periodic graph, the image of
its space group is its point group.

## ii. Key results

- `Crystal.Symmetry.shift` : shift the sites of each label by a lattice vector.
- `Crystal.Symmetry.linear` : rotate or reflect the lattice and permute the labels.
- `Crystal.Symmetry.semidirectEquiv` : the symmetry group is the semidirect product of the shifts
  and the point operations.
- `Crystal.Symmetry.pointHom` : the homomorphism sending a symmetry to its point operation.
- `Crystal.Symmetry.ker_pointHom` : the symmetries with trivial point operation are the shifts.
- `Crystal.PeriodicGraph.pointGroup` : the point operations of the space group of a periodic graph.

## iii. Table of contents

- A. Shifts and point operations
- B. The semidirect product
- C. The point operation of a symmetry
- D. The point group of a periodic graph

## iv. References

* N. Ashcroft & N. D. Mermin, Solid State Physics, Chapter 7.

-/

@[expose] public section

namespace Physlib.CondensedMatter.Crystal

variable {G : Type*} [AddCommGroup G] [AddGroup.FG G]

namespace Symmetry

variable {C : Crystal G}

/-! ## A. Shifts and point operations -/

/-- Move every site with label `i` by the lattice vector `c i`. -/
def shift (C : Crystal G) : Multiplicative (C.UnitCell → G) →* Symmetry C where
  toFun c :=
    { toEquiv := (siteEquiv C).trans <|
        (Equiv.prodShear (Equiv.refl _) fun i => Equiv.addRight (Multiplicative.toAdd c i)).trans
          (siteEquiv C).symm
      lattice := AddEquiv.refl G
      map_vadd := fun _ _ => Site.ext (add_assoc _ _ _) rfl }
  map_one' := Symmetry.ext fun x => Site.ext (by simp [siteEquiv]) rfl
  map_mul' c d := Symmetry.ext fun x => Site.ext (by simp [siteEquiv, add_comm, add_left_comm]) rfl

/-- Apply a lattice automorphism to the cells and permute the labels within the cells. -/
def linear (C : Crystal G) :
    Multiplicative (AddAut G) × Equiv.Perm C.UnitCell →* Symmetry C where
  toFun p :=
    { toEquiv := (siteEquiv C).trans <|
        (p.2.prodCongr (Multiplicative.toAdd p.1).toEquiv).trans (siteEquiv C).symm
      lattice := Multiplicative.toAdd p.1
      map_vadd := fun _ _ => Site.ext ((Multiplicative.toAdd p.1).map_add _ _) rfl }
  map_one' := Symmetry.ext fun _ => rfl
  map_mul' _ _ := Symmetry.ext fun _ => rfl

/-- A shift that moves every label by the same vector is a translation. -/
lemma shift_const (a : G) :
    shift C (Multiplicative.ofAdd fun _ => a) = translation C (Multiplicative.ofAdd a) :=
  Symmetry.ext fun _ => Site.ext (add_comm _ _) rfl

/-- A shift does not change the lattice. -/
@[simp] lemma lattice_shift (c : Multiplicative (C.UnitCell → G)) : (shift C c).lattice = .refl G :=
  rfl

/-- The lattice part of a point operation is its lattice automorphism. -/
@[simp] lemma lattice_linear (p : Multiplicative (AddAut G) × Equiv.Perm C.UnitCell) :
    (linear C p).lattice = Multiplicative.toAdd p.1 := rfl

/-! ## B. The semidirect product -/

/-- The lattice automorphism and label permutation act on the shifts by `c ↦ A ∘ c ∘ σ⁻¹`. -/
def shiftAction (C : Crystal G) :
    Multiplicative (AddAut G) × Equiv.Perm C.UnitCell →*
      MulAut (Multiplicative (C.UnitCell → G)) where
  toFun p := (AddEquiv.arrowCongr p.2 (Multiplicative.toAdd p.1)).toMultiplicative
  map_one' := MulEquiv.ext fun _ => rfl
  map_mul' _ _ := MulEquiv.ext fun _ => rfl

/-- Conjugating a shift by a point operation shifts by `A ∘ c ∘ σ⁻¹`. -/
lemma shift_shiftAction (p : Multiplicative (AddAut G) × Equiv.Perm C.UnitCell)
    (c : Multiplicative (C.UnitCell → G)) :
    shift C (shiftAction C p c) = linear C p * shift C c * (linear C p)⁻¹ :=
  Symmetry.ext fun x => Site.ext
    (by simp [shift, shiftAction, linear, siteEquiv])
    (by simp [shift, linear, siteEquiv])

/-- Shifts and point operations assemble into a homomorphism from the semidirect product. -/
def ofSemidirect (C : Crystal G) :
    Multiplicative (C.UnitCell → G) ⋊[shiftAction C]
      (Multiplicative (AddAut G) × Equiv.Perm C.UnitCell) →* Symmetry C :=
  SemidirectProduct.lift (shift C) (linear C) fun p => MonoidHom.ext fun c => by
    simpa [MulAut.conj_apply] using shift_shiftAction p c

/-- A shift and point operation act on a site by `⟨n, i⟩ ↦ ⟨A n + c (σ i), σ i⟩`. -/
lemma ofSemidirect_apply (y : Multiplicative (C.UnitCell → G) ⋊[shiftAction C]
    (Multiplicative (AddAut G) × Equiv.Perm C.UnitCell)) (x : C.Site) :
    ofSemidirect C y x = ⟨Multiplicative.toAdd y.right.1 x.cell +
      Multiplicative.toAdd y.left (y.right.2 x.label), y.right.2 x.label⟩ := rfl

/-- Different shifts and point operations give different symmetries. -/
lemma ofSemidirect_injective : Function.Injective (ofSemidirect C) := by
  refine (injective_iff_map_eq_one _).2 fun y hy => ?_
  have hx := fun x : C.Site => Site.ext_iff.1 (congrArg (fun s : Symmetry C => s x) hy)
  have hσ : y.right.2 = 1 := Equiv.ext fun i => (hx ⟨0, i⟩).2
  exact SemidirectProduct.ext (Multiplicative.toAdd.injective (funext fun i => by
      simpa [ofSemidirect_apply, hσ] using (hx ⟨0, i⟩).1))
    (Prod.ext (Multiplicative.toAdd.injective (congrArg Symmetry.lattice hy)) hσ)

/-- A symmetry moves the site `⟨n, i⟩` by the lattice automorphism from the image of `⟨0, i⟩`. -/
lemma apply_eq (φ : Symmetry C) (n : G) (i : C.UnitCell) :
    φ ⟨n, i⟩ = ⟨φ.lattice n + (φ ⟨0, i⟩).cell, (φ ⟨0, i⟩).label⟩ := by
  simpa [Site.vadd_def] using φ.map_vadd n ⟨0, i⟩

/-- The label of the image of `⟨n, i⟩` does not depend on the cell `n`. -/
lemma label_apply (φ : Symmetry C) (n : G) (i : C.UnitCell) :
    (φ ⟨n, i⟩).label = (φ ⟨0, i⟩).label := by
  rw [apply_eq φ n i]

/-- A symmetry permutes the labels of the sites; its inverse permutes them back. -/
def labelPerm (φ : Symmetry C) : Equiv.Perm C.UnitCell where
  toFun i := (φ ⟨0, i⟩).label
  invFun j := (φ⁻¹ ⟨0, j⟩).label
  left_inv i := by
    change (φ⁻¹ ⟨0, (φ ⟨0, i⟩).label⟩).label = i
    rw [← label_apply φ⁻¹ (φ ⟨0, i⟩).cell]
    exact congrArg Site.label (φ.toEquiv.symm_apply_apply ⟨0, i⟩)
  right_inv j := by
    change (φ ⟨0, (φ⁻¹ ⟨0, j⟩).label⟩).label = j
    rw [← label_apply φ (φ⁻¹ ⟨0, j⟩).cell]
    exact congrArg Site.label (φ.toEquiv.apply_symm_apply ⟨0, j⟩)

/-- The label permutation of a symmetry sends `i` to the label of the image of `⟨0, i⟩`. -/
lemma labelPerm_apply (φ : Symmetry C) (i : C.UnitCell) :
    labelPerm φ i = (φ ⟨0, i⟩).label := rfl

/-- The shifts and point operation of a symmetry. -/
def toSemidirect (φ : Symmetry C) : Multiplicative (C.UnitCell → G) ⋊[shiftAction C]
    (Multiplicative (AddAut G) × Equiv.Perm C.UnitCell) :=
  ⟨Multiplicative.ofAdd fun j => (φ ⟨0, (labelPerm φ).symm j⟩).cell,
    (Multiplicative.ofAdd φ.lattice, labelPerm φ)⟩

/-- A symmetry is the shifts followed by the point operation that it determines. -/
lemma ofSemidirect_toSemidirect (φ : Symmetry C) : ofSemidirect C (toSemidirect φ) = φ :=
  Symmetry.ext fun x => by
    rw [ofSemidirect_apply, apply_eq]
    exact Site.ext (by simp [toSemidirect]) rfl

/-- Every symmetry is a shift followed by a point operation. -/
lemma exists_eq_shift_mul_linear (φ : Symmetry C) :
    ∃ (c : Multiplicative (C.UnitCell → G)) (σ : Equiv.Perm C.UnitCell),
      φ = shift C c * linear C (Multiplicative.ofAdd φ.lattice, σ) :=
  ⟨_, _, (ofSemidirect_toSemidirect φ).symm⟩

/-- **The symmetry group of a crystal is the semidirect product of the lattice shifts of each
label with the lattice automorphisms and label permutations.** -/
def semidirectEquiv (C : Crystal G) :
    Multiplicative (C.UnitCell → G) ⋊[shiftAction C]
      (Multiplicative (AddAut G) × Equiv.Perm C.UnitCell) ≃* Symmetry C where
  toFun := ofSemidirect C
  invFun := toSemidirect
  left_inv _ := ofSemidirect_injective (ofSemidirect_toSemidirect _)
  right_inv := ofSemidirect_toSemidirect
  map_mul' := map_mul _

/-! ## C. The point operation of a symmetry -/

/-- The point operation of a symmetry: its lattice automorphism and its permutation of the
labels. For `ℤᵈ` the first component is the rotation or reflection of the lattice. -/
def pointHom (C : Crystal G) :
    Symmetry C →* Multiplicative (AddAut G) × Equiv.Perm C.UnitCell :=
  (SemidirectProduct.rightHom (φ := shiftAction C)).comp (semidirectEquiv C).symm

/-- The point operation of a symmetry from the semidirect product is its second factor. -/
lemma pointHom_semidirectEquiv (y : Multiplicative (C.UnitCell → G) ⋊[shiftAction C]
    (Multiplicative (AddAut G) × Equiv.Perm C.UnitCell)) :
    pointHom C (semidirectEquiv C y) = y.right := by
  simp [pointHom]

/-- The symmetries that do not change the lattice or the labels are exactly the shifts. -/
lemma ker_pointHom : (pointHom C).ker = (shift C).range := by
  have := MonoidHom.ker_comp_mulEquiv (SemidirectProduct.rightHom (φ := shiftAction C))
    (semidirectEquiv C).symm
  rw [pointHom, this, ← SemidirectProduct.range_inl_eq_ker_rightHom, ← MonoidHom.range_comp]
  exact congrArg MonoidHom.range (MonoidHom.ext fun c => Symmetry.ext fun _ => rfl)

/-- The linear part of a symmetry is the first component of its point operation. -/
lemma pointHom_fst (φ : Symmetry C) : (pointHom C φ).1 = latticeHom C φ := rfl

/-- Translations have trivial point operation. -/
lemma translations_le_ker_pointHom : translations C ≤ (pointHom C).ker := by
  rw [ker_pointHom]
  rintro _ ⟨a, rfl⟩
  exact ⟨_, shift_const (Multiplicative.toAdd a)⟩

end Symmetry

/-! ## D. The point group of a periodic graph -/

namespace PeriodicGraph

/-- The point group of a periodic graph: the point operations of the symmetries that preserve its
bonds. -/
def pointGroup {C : Crystal G} (g : PeriodicGraph C) :
    Subgroup (Multiplicative (AddAut G) × Equiv.Perm C.UnitCell) :=
  g.spaceGroup.map (Symmetry.pointHom C)

/-- The point group is the image of the space group under the point operation. -/
lemma mem_pointGroup_iff {C : Crystal G} (g : PeriodicGraph C)
    (p : Multiplicative (AddAut G) × Equiv.Perm C.UnitCell) :
    p ∈ g.pointGroup ↔ ∃ φ ∈ g.spaceGroup, Symmetry.pointHom C φ = p :=
  Subgroup.mem_map

end PeriodicGraph

end Physlib.CondensedMatter.Crystal
