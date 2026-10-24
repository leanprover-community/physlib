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

A symmetry of a crystal is determined by where it sends the reference cell.

## i. Overview

Every site is a copy of a site in the reference cell. A symmetry carries each lattice step to
another lattice step by one automorphism `A`, and it sends the reference site with label `i` to a
site `(bᵢ, σ i)`: the labels are permuted by `σ`, and the cell of the image is shifted by `bᵢ`.
These three pieces of data determine the symmetry,

`φ (n, i) = (A n + bᵢ, σ i)`,

and any such data gives a symmetry. This is how crystallographers split a symmetry into a shift of
the atoms along the lattice and a point operation that turns the lattice and permutes the kinds of
atom. The product of two symmetries is then read off from the data.

Ignoring the shifts leaves the point operations alone, which is the point group of crystallography
once geometry is added. The symmetries without a point operation are exactly the shifts.

## ii. Key results

- `Crystal.Symmetry.ofData` : the symmetry `(n, i) ↦ (A n + b i, σ i)` with lattice automorphism
  `A`, label permutation `σ` and offsets `b`.
- `Crystal.Symmetry.eq_ofData` : every symmetry is of this form, with `A`, `σ` and `b` its lattice
  automorphism, `labelHom` and `offset`.
- `Crystal.Symmetry.ofData_mul` : the product is
  `(A, σ, b) * (A', σ', b') = (A + A', σ * σ', A ∘ b' + b ∘ σ')`.
- `Crystal.Symmetry.semidirectEquiv` : the symmetry group is isomorphic to the semidirect product
  `(F → G) ⋊ (Aut G × Sym F)` of the shifts and the point operations.
- `Crystal.Symmetry.pointOp` : the point operation of a symmetry, a homomorphism.
- `Crystal.Symmetry.pointOp_eq_one_iff` : the symmetries with trivial point operation are the
  shifts.

## iii. Table of contents

- A. The data of a symmetry
- B. Shifts and point operations
- C. The semidirect product
- D. The point operation of a symmetry

## iv. References

* N. Ashcroft & N. D. Mermin, Solid State Physics, Chapter 7.

-/

@[expose] public section

namespace Physlib.CondensedMatter.Crystal

variable {G : Type*} [AddCommGroup G] [AddGroup.FG G]

namespace Symmetry

variable {C : Crystal G}

/-! ## A. The data of a symmetry -/

/-- The label of the image of `⟨n, i⟩` does not depend on the cell `n`. -/
lemma label_apply (φ : Symmetry C) (n : G) (i : C.UnitCell) :
    (φ ⟨n, i⟩).label = (φ ⟨0, i⟩).label := by
  rw [apply_eq φ n i]

/-- A symmetry permutes the labels: it sends `i` to the label of the image of `⟨0, i⟩`. -/
instance : MulAction (Symmetry C) C.UnitCell where
  smul φ i := (φ ⟨0, i⟩).label
  one_smul _ := rfl
  mul_smul φ ψ i := label_apply φ (ψ ⟨0, i⟩).cell (ψ ⟨0, i⟩).label

/-- The permutation of the labels by a symmetry, as a homomorphism. -/
noncomputable def labelHom (C : Crystal G) : Symmetry C →* Equiv.Perm C.UnitCell :=
  MulAction.toPermHom (Symmetry C) C.UnitCell

/-- The label permutation of a symmetry sends `i` to the label of the image of `⟨0, i⟩`. -/
lemma labelHom_apply (φ : Symmetry C) (i : C.UnitCell) :
    labelHom C φ i = (φ ⟨0, i⟩).label := rfl

/-- The offset of a symmetry at the label `i`: the cell of the image of the reference site
`⟨0, i⟩`. -/
def offset (φ : Symmetry C) (i : C.UnitCell) : G := (φ ⟨0, i⟩).cell

/-- A symmetry moves the site `⟨n, i⟩` to the cell `A n + b i` and the label `σ i`. -/
lemma apply_eq_data (φ : Symmetry C) (x : C.Site) :
    φ x = ⟨φ.lattice x.cell + φ.offset x.label, labelHom C φ x.label⟩ :=
  apply_eq φ x.cell x.label

/-- The cell of the image of a site. -/
lemma cell_apply (φ : Symmetry C) (x : C.Site) :
    (φ x).cell = φ.lattice x.cell + φ.offset x.label :=
  congrArg Site.cell (apply_eq_data φ x)

/-- The permutation of the sites `⟨n, i⟩ ↦ ⟨A n + b i, σ i⟩`. -/
def dataEquiv (C : Crystal G) (A : G ≃+ G) (σ : Equiv.Perm C.UnitCell) (b : C.UnitCell → G) :
    C.Site ≃ C.Site where
  toFun x := ⟨A x.cell + b x.label, σ x.label⟩
  invFun x := ⟨A.symm (x.cell - b (σ.symm x.label)), σ.symm x.label⟩
  left_inv x := Site.ext (by simp) (by simp)
  right_inv x := Site.ext (by simp) (by simp)

/-- The symmetry with lattice automorphism `A`, label permutation `σ` and offsets `b`. -/
def ofData (C : Crystal G) (A : G ≃+ G) (σ : Equiv.Perm C.UnitCell) (b : C.UnitCell → G) :
    Symmetry C :=
  ⟨A, { toFun := dataEquiv C A σ b
        map_vadd' _ _ := Site.ext (by simp [dataEquiv, Site.vadd_def, add_assoc]) rfl },
    (dataEquiv C A σ b).bijective⟩

/-- The symmetry given by data moves `⟨n, i⟩` to `⟨A n + b i, σ i⟩`. -/
@[simp] lemma ofData_apply (A : G ≃+ G) (σ : Equiv.Perm C.UnitCell) (b : C.UnitCell → G)
    (x : C.Site) : ofData C A σ b x = ⟨A x.cell + b x.label, σ x.label⟩ := rfl

@[simp] lemma lattice_ofData (A : G ≃+ G) (σ : Equiv.Perm C.UnitCell) (b : C.UnitCell → G) :
    (ofData C A σ b).lattice = A := rfl

@[simp] lemma labelHom_ofData (A : G ≃+ G) (σ : Equiv.Perm C.UnitCell) (b : C.UnitCell → G) :
    labelHom C (ofData C A σ b) = σ :=
  Equiv.ext (congrFun rfl)

@[simp] lemma offset_ofData (A : G ≃+ G) (σ : Equiv.Perm C.UnitCell) (b : C.UnitCell → G) :
    (ofData C A σ b).offset = b := by
  ext i
  show A 0 + b i = b i
  rw [map_zero, zero_add]

/-- Every symmetry is given by its lattice automorphism, label permutation and offsets. -/
lemma eq_ofData (φ : Symmetry C) : φ = ofData C φ.lattice (labelHom C φ) φ.offset := by
  ext x : 1
  exact apply_eq_data φ x

/-- The product of two symmetries, from their data.
`(A, σ, b) * (A', σ', b') = (A + A', σ * σ', A ∘ b' + b ∘ σ')`, where `A + A'` is the composite
`A ∘ A'`. -/
lemma ofData_mul (A B : G ≃+ G) (σ τ : Equiv.Perm C.UnitCell) (b b' : C.UnitCell → G) :
    ofData C A σ b * ofData C B τ b' = ofData C (A + B) (σ * τ) (A ∘ b' + b ∘ τ) := by
  ext x : 1
  refine Site.ext ?_ rfl
  show A (B x.cell + b' x.label) + b (τ x.label) = (A + B) x.cell + (A (b' x.label) + b (τ x.label))
  rw [map_add, add_assoc]
  rfl

/-! ## B. Shifts and point operations -/

/-- Move every site with label `i` by the lattice vector `c i`. -/
def shift (C : Crystal G) (c : C.UnitCell → G) : Symmetry C := ofData C 0 1 c

/-- Apply the lattice automorphism `A` to the cells and permute the labels within the cells by
`σ`. -/
def linear (C : Crystal G) (A : G ≃+ G) (σ : Equiv.Perm C.UnitCell) : Symmetry C :=
  ofData C A σ 0

/-- A shift that moves every label by the same vector is a translation. -/
lemma shift_const (a : G) : shift C (Function.const C.UnitCell a) = translation C a := by
  ext x : 1
  exact Site.ext (add_comm _ _) rfl

/-- A shift does not change the lattice. -/
@[simp] lemma lattice_shift (c : C.UnitCell → G) : (shift C c).lattice = 0 := rfl

/-- The lattice part of a point operation is its lattice automorphism. -/
@[simp] lemma lattice_linear (A : G ≃+ G) (σ : Equiv.Perm C.UnitCell) :
    (linear C A σ).lattice = A := rfl

/-- A point operation moves `⟨n, i⟩` to `⟨A n, σ i⟩`. -/
@[simp] lemma linear_apply (A : G ≃+ G) (σ : Equiv.Perm C.UnitCell) (x : C.Site) :
    linear C A σ x = ⟨A x.cell, σ x.label⟩ :=
  Site.ext (add_zero _) rfl

/-- A shift followed by a point operation is the symmetry with offsets `c ∘ σ`. -/
lemma shift_mul_linear (c : C.UnitCell → G) (A : G ≃+ G) (σ : Equiv.Perm C.UnitCell) :
    shift C c * linear C A σ = ofData C A σ (c ∘ σ) := by
  show ofData C 0 1 c * ofData C A σ 0 = _
  rw [ofData_mul]
  simp

@[simp] lemma labelHom_shift_mul_linear (c : C.UnitCell → G) (A : G ≃+ G)
    (σ : Equiv.Perm C.UnitCell) : labelHom C (shift C c * linear C A σ) = σ := by
  rw [shift_mul_linear, labelHom_ofData]

@[simp] lemma offset_shift_mul_linear (c : C.UnitCell → G) (A : G ≃+ G)
    (σ : Equiv.Perm C.UnitCell) : (shift C c * linear C A σ).offset = c ∘ σ := by
  rw [shift_mul_linear, offset_ofData]

/-- Shifts add. -/
lemma shift_add (c d : C.UnitCell → G) : shift C (c + d) = shift C c * shift C d := by
  show ofData C 0 1 (c + d) = ofData C 0 1 c * ofData C 0 1 d
  rw [ofData_mul]
  simp [add_comm]

/-- Point operations compose. -/
lemma linear_add_mul (A B : G ≃+ G) (σ τ : Equiv.Perm C.UnitCell) :
    linear C (A + B) (σ * τ) = linear C A σ * linear C B τ := by
  show ofData C (A + B) (σ * τ) 0 = ofData C A σ 0 * ofData C B τ 0
  rw [ofData_mul]
  simp

/-- The product of shifts and point operations. With `A + B` the composite `A ∘ B`,
`(c, A, σ) * (c', B, τ) = (c + A ∘ c' ∘ σ⁻¹, A + B, σ * τ)`. -/
lemma shift_mul_linear_mul (c c' : C.UnitCell → G) (A B : G ≃+ G) (σ τ : Equiv.Perm C.UnitCell) :
    (shift C c * linear C A σ) * (shift C c' * linear C B τ) =
      shift C (c + A ∘ c' ∘ σ.symm) * linear C (A + B) (σ * τ) := by
  rw [shift_mul_linear, shift_mul_linear, shift_mul_linear, ofData_mul]
  congr 1
  ext i
  simp [add_comm]

/-! ## C. The semidirect product -/

/-- The lattice automorphism and label permutation act on the shifts by `c ↦ A ∘ c ∘ σ⁻¹`. -/
def shiftAction (C : Crystal G) :
    Multiplicative (AddAut G) × Equiv.Perm C.UnitCell →*
      MulAut (Multiplicative (C.UnitCell → G)) where
  toFun p := (AddEquiv.arrowCongr p.2 (Multiplicative.toAdd p.1)).toMultiplicative
  map_one' := MulEquiv.ext (congrFun rfl)
  map_mul' _ _ := MulEquiv.ext (congrFun rfl)

/-- Every symmetry is a point operation followed by a shift. -/
lemma eq_shift_mul_linear (φ : Symmetry C) :
    φ = shift C (φ.offset ∘ (labelHom C φ).symm) * linear C φ.lattice (labelHom C φ) := by
  have h : (φ.offset ∘ ⇑(labelHom C φ).symm) ∘ ⇑(labelHom C φ) = φ.offset := by
    ext i
    simp
  rw [shift_mul_linear, h]
  exact eq_ofData φ

/-- The symmetry group of a crystal is the semidirect product of the shifts of each label with
the lattice automorphisms and label permutations. -/
noncomputable def semidirectEquiv (C : Crystal G) :
    Multiplicative (C.UnitCell → G) ⋊[shiftAction C]
      (Multiplicative (AddAut G) × Equiv.Perm C.UnitCell) ≃* Symmetry C where
  toFun y := shift C (Multiplicative.toAdd y.left) *
    linear C (Multiplicative.toAdd y.right.1) y.right.2
  invFun φ := ⟨Multiplicative.ofAdd (φ.offset ∘ (labelHom C φ).symm),
    Multiplicative.ofAdd φ.lattice, labelHom C φ⟩
  left_inv y := by
    refine SemidirectProduct.ext (Multiplicative.toAdd.injective ?_) (Prod.ext (by simp) (by simp))
    ext i
    simp
  right_inv φ := (eq_shift_mul_linear φ).symm
  map_mul' _ _ := (shift_mul_linear_mul _ _ _ _ _ _).symm

/-! ## D. The point operation of a symmetry -/

/-- The point operation of a symmetry: keep its lattice automorphism and its permutation of the
labels, and drop the shifts. It fixes the reference cell's position, so for `ℤᵈ` it is the rotation
or reflection of the lattice. -/
noncomputable def pointOp (C : Crystal G) : Symmetry C →* Symmetry C where
  toFun φ := linear C φ.lattice (labelHom C φ)
  map_one' := by
    ext x : 1
    exact Site.ext (add_zero _) rfl
  map_mul' φ ψ := by
    rw [lattice_mul, map_mul]
    exact linear_add_mul _ _ _ _

/-- Every symmetry is a shift followed by its point operation. -/
lemma exists_eq_shift_mul_pointOp (φ : Symmetry C) : ∃ c, φ = shift C c * pointOp C φ :=
  ⟨_, eq_shift_mul_linear φ⟩

/-- The point operation of a shift is trivial. -/
@[simp] lemma pointOp_shift (c : C.UnitCell → G) : pointOp C (shift C c) = 1 := by
  ext x : 1
  exact Site.ext (add_zero _) rfl

/-- The symmetries with trivial point operation are exactly the shifts. -/
lemma pointOp_eq_one_iff (φ : Symmetry C) : pointOp C φ = 1 ↔ ∃ c, φ = shift C c := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := exists_eq_shift_mul_pointOp φ
    exact ⟨c, by rw [hc, h, mul_one]⟩
  · rintro ⟨c, rfl⟩
    exact pointOp_shift c

/-- Translations have trivial point operation. -/
lemma pointOp_translation (a : G) : pointOp C (translation C a) = 1 := by
  rw [← shift_const]
  exact pointOp_shift _

end Symmetry

end Physlib.CondensedMatter.Crystal
