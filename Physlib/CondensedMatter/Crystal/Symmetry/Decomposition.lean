/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.CondensedMatter.Crystal.Symmetry.Basic
public import Mathlib.GroupTheory.SemidirectProduct

/-!
# Decomposition of crystal symmetries

Every crystal symmetry is a lattice automorphism, a permutation of labels and a shift.

## i. Overview

A symmetry sends all sites with the same label to sites with one common label, so it permutes
the labels of the unit cell by a permutation `σ`. It maps the lattice vectors by an automorphism
`A` and moves the sites with label `j` by a lattice vector `s j`. These three pieces describe its
action on every site:

`⟨n, i⟩ ↦ ⟨A n + s (σ i), σ i⟩`.

Conversely every choice of `A`, `σ` and `s` defines a symmetry. In graphene, shifting only the
carbon atoms of one sublattice by a lattice vector is a symmetry with `A = 1` and `σ = 1`. It is
not a translation.

Composing two symmetries composes their automorphisms and permutations. The shifts of the second
symmetry are transformed by `A` and relabelled by `σ` before they are added. The symmetry group is
therefore the semidirect product of the shifts by the lattice automorphisms and label
permutations.

## ii. Key results

- `Crystal.Symmetry.labelPerm` : the permutation `σ` of the labels of a symmetry.
- `Crystal.Symmetry.shift` : the shifts `s` of a symmetry.
- `Crystal.Symmetry.apply_eq` : a symmetry acts as `⟨n, i⟩ ↦ ⟨A n + s (σ i), σ i⟩`.
- `Crystal.Symmetry.ofParts` : the symmetry built from `A`, `σ` and `s`.
- `Crystal.Symmetry.semidirectEquiv` : the symmetry group is the semidirect product of the shifts
  by the lattice automorphisms and label permutations.

## iii. Table of contents

- A. The permutation of labels
- B. The shifts of a symmetry
- C. Symmetries from their parts
- D. The semidirect product

## iv. References

* None.

-/

@[expose] public section

namespace Physlib.CondensedMatter.Crystal

variable {G : Type*} [AddCommGroup G] [AddGroup.FG G]

namespace Symmetry

variable {C : Crystal G}

/-! ## A. The permutation of labels -/

/-- The label of an image site depends only on the label of the site. -/
lemma label_apply (φ : Symmetry C) (x : C.Site) :
    (φ x).label = (φ (Site.ref x.label)).label := by
  conv_lhs => rw [show x = x.cell +ᵥ Site.ref x.label from Site.ext (add_zero _).symm rfl]
  rw [map_vadd]
  rfl

/-- Symmetries permute the labels of the unit cell. -/
instance : MulAction (Symmetry C) C.UnitCell where
  smul φ i := (φ (Site.ref i)).label
  one_smul _ := rfl
  mul_smul φ ψ i := label_apply φ (ψ (Site.ref i))

/-- The permutation of labels of a symmetry. -/
def labelPerm (φ : Symmetry C) : Equiv.Perm C.UnitCell := MulAction.toPerm φ

@[simp] lemma labelPerm_apply (φ : Symmetry C) (i : C.UnitCell) : φ.labelPerm i = φ • i := rfl

/-! ## B. The shifts of a symmetry -/

/-- The shift of a symmetry at the label `j`: the cell of the image of the reference site that
the symmetry sends to label `j`. -/
def shift (φ : Symmetry C) (j : C.UnitCell) : G := (φ (Site.ref (φ⁻¹ • j))).cell

/-- A symmetry acts as `⟨n, i⟩ ↦ ⟨A n + s (σ i), σ i⟩`. -/
lemma apply_eq (φ : Symmetry C) (x : C.Site) :
    φ x = ⟨φ.latticeAut x.cell + φ.shift (φ.labelPerm x.label), φ.labelPerm x.label⟩ := by
  rw [labelPerm_apply, shift, inv_smul_smul]
  calc φ x = φ (x.cell +ᵥ Site.ref x.label) := congrArg φ (Site.ext (add_zero _).symm rfl)
    _ = _ := φ.map_vadd _ _

/-! ## C. Symmetries from their parts -/

/-- The symmetry `⟨n, i⟩ ↦ ⟨A n + s (σ i), σ i⟩` with lattice automorphism `A`, label
permutation `σ` and shifts `s`. -/
def ofParts (C : Crystal G) (A : G ≃+ G) (σ : Equiv.Perm C.UnitCell) (s : C.UnitCell → G) :
    Symmetry C where
  toFun x := ⟨A x.cell + s (σ x.label), σ x.label⟩
  invFun y := ⟨A.symm (y.cell - s y.label), σ.symm y.label⟩
  left_inv x := Site.ext (by simp) (σ.symm_apply_apply _)
  right_inv y := Site.ext (by simp) (σ.apply_symm_apply _)
  latticeAut := A
  map_vadd' a x := Site.ext (by simp [Site.vadd_def, add_assoc]) rfl

variable (A B : G ≃+ G) (σ τ : Equiv.Perm C.UnitCell) (s t : C.UnitCell → G)

@[simp] lemma ofParts_apply (x : C.Site) :
    ofParts C A σ s x = ⟨A x.cell + s (σ x.label), σ x.label⟩ := rfl

@[simp] lemma latticeAut_ofParts : (ofParts C A σ s).latticeAut = A := rfl

@[simp] lemma labelPerm_ofParts : (ofParts C A σ s).labelPerm = σ := rfl

@[simp] lemma shift_ofParts : (ofParts C A σ s).shift = s := by
  ext j
  change A 0 + s (σ (σ.symm j)) = s j
  simp

/-- Every symmetry is built from its lattice automorphism, label permutation and shifts. -/
lemma ofParts_eq (φ : Symmetry C) :
    ofParts C φ.latticeAut φ.labelPerm φ.shift = φ := by
  ext x : 1
  rw [apply_eq φ x]
  rfl

/-- Composition composes the automorphisms and permutations. The shifts of the second symmetry
are transformed by `A` and relabelled by `σ`. -/
lemma ofParts_mul :
    ofParts C A σ s * ofParts C B τ t = ofParts C (B.trans A) (σ * τ) (s + A ∘ t ∘ σ.symm) := by
  ext x : 1
  refine Site.ext ?_ rfl
  simp [map_add, add_left_comm, add_comm]

/-! ## D. The semidirect product -/

/-- Lattice automorphisms and label permutations act on shifts by `s ↦ A ∘ s ∘ σ⁻¹`. -/
def shiftAction (C : Crystal G) :
    Multiplicative (AddAut G) × Equiv.Perm C.UnitCell →*
      MulAut (Multiplicative (C.UnitCell → G)) where
  toFun p := (AddEquiv.arrowCongr p.2 (Multiplicative.toAdd p.1)).toMultiplicative
  map_one' := MulEquiv.ext (congrFun rfl)
  map_mul' _ _ := MulEquiv.ext (congrFun rfl)

/-- The symmetry group is the semidirect product of the shifts by the lattice automorphisms and
label permutations. -/
def semidirectEquiv (C : Crystal G) :
    Multiplicative (C.UnitCell → G) ⋊[shiftAction C]
      (Multiplicative (AddAut G) × Equiv.Perm C.UnitCell) ≃* Symmetry C where
  toFun y := ofParts C (Multiplicative.toAdd y.right.1) y.right.2 (Multiplicative.toAdd y.left)
  invFun φ := ⟨Multiplicative.ofAdd φ.shift, Multiplicative.ofAdd φ.latticeAut,
    φ.labelPerm⟩
  left_inv y := SemidirectProduct.ext (by simp) (Prod.ext rfl (Equiv.ext (congrFun rfl)))
  right_inv := ofParts_eq
  map_mul' x y := (ofParts_mul _ _ _ _ _ _).symm

end Symmetry

end Physlib.CondensedMatter.Crystal
