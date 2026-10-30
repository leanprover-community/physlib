/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.CondensedMatter.Crystal.Symmetry.Basic
public import Mathlib.GroupTheory.SemidirectProduct

/-!
# Shifts and point operations of a crystal

A symmetry of a crystal is determined by where it sends the reference cell.

## i. Overview

A crystal is built by repeating a unit cell across a lattice. Its symmetries may transform the
lattice, permute the sites within the unit cell or move them between cells.

Remarkably, every symmetry is determined by just three ingredients: a lattice automorphism `A`, a
permutation `σ` of the unit-cell labels and an offset `bᵢ` for each label. Together they describe
the action on any site:

`(n, i) ↦ (A n + bᵢ, σ i)`.

This allows every symmetry to be decomposed into a shift and a point operation. The symmetry group
is consequently a semidirect product of these two groups.

The construction is entirely algebraic and requires no embedding into Euclidean space. It provides
the foundation for studying crystallographic symmetries once geometry is introduced.

## ii. Key results

- `Crystal.Symmetry.ofSemidirect` : the symmetry `(n, i) ↦ (A n + b (σ i), σ i)` of a shift `b`
  followed by a lattice automorphism `A` and a label permutation `σ`.
- `Crystal.Symmetry.semidirectEquiv` : the symmetry group is isomorphic to the semidirect product
  `(F → G) ⋊ (Aut G × Sym F)` of the shifts and the point operations.
- `Crystal.Symmetry.shift` and `Crystal.Symmetry.linear` : the symmetries with only offsets and the
  symmetries with only a lattice automorphism and a label permutation.
- `Crystal.Symmetry.pointOp` : the point operation of a symmetry, a homomorphism.
- `Crystal.Symmetry.pointOp_eq_one_iff` : the symmetries with trivial point operation are the
  shifts.

## iii. Table of contents

- A. The symmetry group as a semidirect product
- B. Shifts and point operations

## iv. References

* F. Göhmann, *Introduction to Solid State Physics*, lecture L4, Sections 4.3 and 4.4.
  [ref: goehmann_solid_state_2021]

-/

@[expose] public section

namespace Physlib.CondensedMatter.Crystal

variable {G : Type*} [AddCommGroup G] [AddGroup.FG G]

namespace Symmetry

variable {C : Crystal G} (A B : G ≃+ G) (σ τ : Equiv.Perm C.UnitCell)
  (b b' : Offsets C)

/-! ## A. The symmetry group as a semidirect product -/

/-- The action of the point operations on the shifts: a lattice automorphism `A` and a label
permutation `σ` send `b` to `A ∘ b ∘ σ⁻¹`. -/
def shiftAction (C : Crystal G) :
    Multiplicative (AddAut G) × Equiv.Perm C.UnitCell →*
      MulAut (Multiplicative (Offsets C)) where
  toFun p := (AddEquiv.arrowCongr p.2 (Multiplicative.toAdd p.1)).toMultiplicative
  map_one' := MulEquiv.ext (congrFun rfl)
  map_mul' _ _ := MulEquiv.ext (congrFun rfl)

/-- The shifts and point operations of a crystal: the semidirect product of the shifts by the
lattice automorphisms and label permutations. -/
abbrev ShiftPointOp (C : Crystal G) :=
  Multiplicative (Offsets C) ⋊[shiftAction C] (Multiplicative (AddAut G) × Equiv.Perm C.UnitCell)

/-- The bijection of the sites of the element `(b, (A, σ))`: it sends `⟨n, i⟩` to
`⟨A n + b (σ i), σ i⟩`. -/
def ofSemidirectEquiv (C : Crystal G) (y : ShiftPointOp C) : C.Site ≃ C.Site where
  toFun x := ⟨Multiplicative.toAdd y.right.1 x.cell +
    Multiplicative.toAdd y.left (y.right.2 x.label), y.right.2 x.label⟩
  invFun x := ⟨(Multiplicative.toAdd y.right.1).symm
    (x.cell - Multiplicative.toAdd y.left x.label), y.right.2.symm x.label⟩
  left_inv x := Site.ext (by simp) (by simp)
  right_inv x := Site.ext (by simp) (by simp)

/-- The symmetry of the element `(b, (A, σ))`: it has the lattice automorphism `A` and sends
`⟨n, i⟩` to `⟨A n + b (σ i), σ i⟩`. -/
def ofSemidirect (C : Crystal G) (y : ShiftPointOp C) : Symmetry C :=
  ⟨Multiplicative.toAdd y.right.1,
    { toFun := ofSemidirectEquiv C y
      map_vadd' _ _ := Site.ext (by simp [ofSemidirectEquiv, Site.vadd_def, add_assoc]) rfl },
    (ofSemidirectEquiv C y).bijective⟩

/-- `ofSemidirect C (b, (A, σ))` sends `⟨n, i⟩` to `⟨A n + b (σ i), σ i⟩`. -/
@[simp] lemma ofSemidirect_apply (y : ShiftPointOp C) (x : C.Site) :
    ofSemidirect C y x = ofSemidirectEquiv C y x := rfl

/-- The lattice automorphism of `ofSemidirect C (b, (A, σ))` is `A`. -/
@[simp] lemma lattice_ofSemidirect (y : ShiftPointOp C) :
    (ofSemidirect C y).lattice = Multiplicative.toAdd y.right.1 := rfl

/-- The label permutation of `ofSemidirect C (b, (A, σ))` is `σ`. -/
@[simp] lemma labelHom_ofSemidirect (y : ShiftPointOp C) :
    labelHom C (ofSemidirect C y) = y.right.2 :=
  Equiv.ext (congrFun rfl)

/-- The symmetry of a product is the product of the symmetries. -/
lemma ofSemidirect_mul (x y : ShiftPointOp C) :
    ofSemidirect C (x * y) = ofSemidirect C x * ofSemidirect C y := by
  ext z : 1
  refine Site.ext ?_ rfl
  simp [ofSemidirectEquiv, shiftAction, AddEquiv.arrowCongr]
  rw [← add_assoc, add_right_comm]

/-- The symmetry group of a crystal is isomorphic to the semidirect product of the shifts, `UnitCell
→ G`, by the point operations, `Aut G × Perm UnitCell`, acting through `shiftAction`. -/
noncomputable def semidirectEquiv (C : Crystal G) : ShiftPointOp C ≃* Symmetry C where
  toFun := ofSemidirect C
  invFun φ := ⟨Multiplicative.ofAdd (φ.offset ∘ (labelHom C φ).symm),
    Multiplicative.ofAdd φ.lattice, labelHom C φ⟩
  left_inv y := by
    refine SemidirectProduct.ext (Multiplicative.toAdd.injective ?_)
      (Prod.ext (by simp) (by simp))
    ext i
    simp [ofSemidirectEquiv, offset]
  right_inv φ := by
    ext x : 1
    refine Site.ext ?_ ?_
    · simp [ofSemidirectEquiv, cell_apply]
    · exact (label_apply φ x.cell x.label).symm
  map_mul' := ofSemidirect_mul

/-! ## B. Shifts and point operations -/

/-- The shift by `b`: it moves every site with label `i` by the lattice vector `bᵢ` and fixes the
labels and the lattice. -/
noncomputable def shift (C : Crystal G) (b : Offsets C) : Symmetry C :=
  semidirectEquiv C (SemidirectProduct.inl (Multiplicative.ofAdd b))

/-- The point operation with lattice automorphism `A` and label permutation `σ`: it sends `⟨n, i⟩`
to `⟨A n, σ i⟩` and has no offsets. -/
noncomputable def linear (C : Crystal G) (A : G ≃+ G) (σ : Equiv.Perm C.UnitCell) : Symmetry C :=
  semidirectEquiv C (SemidirectProduct.inr (Multiplicative.ofAdd A, σ))

/-- The point operation of a symmetry: the point operation with the same lattice automorphism and
label permutation, dropping the shifts. It is a homomorphism. For `ℤᵈ` it is the rotation or
reflection of the lattice. -/
noncomputable def pointOp (C : Crystal G) : Symmetry C →* Symmetry C :=
  (semidirectEquiv C).toMonoidHom.comp (SemidirectProduct.inr.comp
    (SemidirectProduct.rightHom.comp (semidirectEquiv C).symm.toMonoidHom))

/-- A shift has trivial lattice automorphism. -/
@[simp] lemma lattice_shift : (shift C b).lattice = 0 := rfl

/-- `shift C b` sends `⟨n, i⟩` to `⟨n + bᵢ, i⟩`. -/
@[simp] lemma shift_apply (x : C.Site) : shift C b x = ⟨x.cell + b x.label, x.label⟩ := rfl

/-- `linear C A σ` sends `⟨n, i⟩` to `⟨A n, σ i⟩`. -/
@[simp] lemma linear_apply (x : C.Site) : linear C A σ x = ⟨A x.cell, σ x.label⟩ :=
  Site.ext (add_zero _) rfl

/-- Shifts compose by adding their vectors: `shift (b + b') = shift b * shift b'`. -/
lemma shift_add : shift C (b + b') = shift C b * shift C b' := by
  rw [shift, shift, shift, ofAdd_add, map_mul, map_mul]

/-- Point operations compose through their components: `linear (A + B) (σ * τ) = linear A σ * linear
B τ`. -/
lemma linear_add_mul : linear C (A + B) (σ * τ) = linear C A σ * linear C B τ := by
  rw [linear, linear, linear, ← map_mul, ← map_mul]
  rfl

/-- A shift by the same vector `a` on every label is the translation by `a`. -/
lemma shift_const (a : G) : shift C (Function.const C.UnitCell a) = translation C a := by
  ext x : 1
  exact Site.ext (add_comm _ _) rfl

/-- Every symmetry is a point operation followed by a shift. -/
lemma exists_eq_shift_mul_pointOp (φ : Symmetry C) : ∃ b, φ = shift C b * pointOp C φ :=
  ⟨Multiplicative.toAdd ((semidirectEquiv C).symm φ).left, by
    simp [shift, pointOp, ← map_mul]⟩

/-- A shift has trivial point operation. -/
@[simp] lemma pointOp_shift : pointOp C (shift C b) = 1 := by
  simp [pointOp, shift]

/-- A symmetry has trivial point operation exactly when it is a shift. -/
lemma pointOp_eq_one_iff (φ : Symmetry C) : pointOp C φ = 1 ↔ ∃ b, φ = shift C b :=
  ⟨fun h => let ⟨b, hb⟩ := exists_eq_shift_mul_pointOp φ; ⟨b, by rw [hb, h, mul_one]⟩,
    by rintro ⟨b, rfl⟩; exact pointOp_shift b⟩

/-- A translation has trivial point operation. -/
lemma pointOp_translation (a : G) : pointOp C (translation C a) = 1 := by
  rw [← shift_const, pointOp_shift]

end Symmetry

end Physlib.CondensedMatter.Crystal
