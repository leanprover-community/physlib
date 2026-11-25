/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.CondensedMatter.Crystal.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Defs

/-!
# Symmetries of a crystal

The operations that leave a crystal unchanged form its symmetry group.

## i. Overview

A crystal looks the same after certain operations, its symmetries. The simplest are
translations by lattice vectors. Other symmetries rotate or reflect the lattice, or exchange
sites within a unit cell. In graphene, inversion through the centre of a bond exchanges the
two carbon atoms of a unit cell.

A symmetry permutes the sites and transforms the lattice vectors by an automorphism `A` of the
translation group, so that

`φ (a +ᵥ x) = A a +ᵥ φ x`.

The same `A` applies everywhere in the crystal. For example, a quarter turn of a square lattice
sends a step to the right to a step upwards.

With one site per cell the symmetries are the affine equivalences of the sites. With several
sites per cell a symmetry may also exchange the sites within a cell. The definition captures the
periodic structure alone. It does not require symmetries to preserve distances, bonds or atomic
species.

Lattice translations form a normal subgroup of the symmetry group.

## ii. Key results

- `Crystal.Symmetry` : a permutation of sites compatible with lattice translations.
- `Crystal.Symmetry.latticeAut` : the induced automorphism of the translation group.
- `Crystal.Symmetry.conj_translation` : conjugation transforms a translation by `a` into one
  by `latticeAut a`.
- `Crystal.Symmetry.translations` : the normal subgroup of lattice translations.

## iii. Table of contents

- A. Crystal symmetries
- B. The symmetry group
  - B.1. Composition and inverses
  - B.2. Actions on sites and lattice vectors
- C. Lattice translations

## iv. References

* None.

-/

@[expose] public section

namespace Physlib.CondensedMatter.Crystal

variable {G : Type*} [AddCommGroup G] [AddGroup.FG G]

/-! ## A. Crystal symmetries -/

/-- A permutation of crystal sites compatible with lattice translations.

The site permutation `φ` and the automorphism `A = latticeAut` satisfy
`φ (a +ᵥ x) = A a +ᵥ φ x` for every lattice vector `a` and site `x`. -/
structure Symmetry (C : Crystal G) extends C.Site ≃ C.Site where
  /-- The automorphism induced on the translation group by the site permutation. -/
  latticeAut : G ≃+ G
  /-- Translating a site by `a` translates its image by `latticeAut a`. -/
  map_vadd' : ∀ (a : G) (x : C.Site), toEquiv (a +ᵥ x) = latticeAut a +ᵥ toEquiv x

namespace Symmetry

variable {C : Crystal G}

/-- The action on sites uniquely determines the action on lattice vectors. -/
lemma latticeAut_eq_of_toEquiv_eq {φ ψ : Symmetry C} (h : φ.toEquiv = ψ.toEquiv) :
    φ.latticeAut = ψ.latticeAut := by
  obtain ⟨x⟩ := (inferInstance : Nonempty C.Site)
  ext a
  refine IsCancelVAdd.right_cancel _ _ (φ.toEquiv x) ?_
  rw [← φ.map_vadd', h, ψ.map_vadd']

/-- A crystal symmetry is an equivalence of its sites. -/
instance : EquivLike (Symmetry C) C.Site C.Site where
  coe φ := φ.toEquiv
  inv φ := φ.toEquiv.symm
  left_inv φ := φ.toEquiv.left_inv
  right_inv φ := φ.toEquiv.right_inv
  coe_injective' φ ψ h _ := by
    obtain ⟨e, A, hA⟩ := φ
    obtain ⟨f, B, hB⟩ := ψ
    obtain rfl : e = f := Equiv.coe_fn_injective h
    obtain rfl : A = B :=
      latticeAut_eq_of_toEquiv_eq (φ := ⟨e, A, hA⟩) (ψ := ⟨e, B, hB⟩) rfl
    rfl

/-- Two symmetries are equal if they agree on every site. -/
@[ext] lemma ext {φ ψ : Symmetry C} (h : ∀ x, φ x = ψ x) : φ = ψ := DFunLike.ext _ _ h

@[simp] lemma coe_toEquiv (φ : Symmetry C) : ⇑φ.toEquiv = φ := rfl

/-- A symmetry maps the translation of a site by `a` to the translation of its image
by `latticeAut a`. -/
lemma map_vadd (φ : Symmetry C) (a : G) (x : C.Site) : φ (a +ᵥ x) = φ.latticeAut a +ᵥ φ x :=
  φ.map_vadd' a x

/-! ## B. The symmetry group -/

/-! ### B.1. Composition and inverses -/

/-- Crystal symmetries form a group under composition of their site permutations. -/
instance : Group (Symmetry C) where
  mul φ ψ := ⟨ψ.toEquiv.trans φ.toEquiv, ψ.latticeAut.trans φ.latticeAut, fun a x => by
    change φ (ψ (a +ᵥ x)) = φ.latticeAut (ψ.latticeAut a) +ᵥ φ (ψ x)
    rw [ψ.map_vadd, φ.map_vadd]⟩
  one := ⟨Equiv.refl _, AddEquiv.refl G, fun _ _ => rfl⟩
  inv φ := ⟨φ.toEquiv.symm, φ.latticeAut.symm, fun a x => φ.toEquiv.injective (by
    rw [φ.map_vadd', Equiv.apply_symm_apply, Equiv.apply_symm_apply, AddEquiv.apply_symm_apply])⟩
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl
  inv_mul_cancel φ := ext φ.toEquiv.symm_apply_apply

@[simp] lemma mul_apply (φ ψ : Symmetry C) (x : C.Site) : (φ * ψ) x = φ (ψ x) := rfl

@[simp] lemma one_apply (x : C.Site) : (1 : Symmetry C) x = x := rfl

@[simp] lemma inv_apply_apply (φ : Symmetry C) (x : C.Site) : φ⁻¹ (φ x) = x :=
  φ.toEquiv.symm_apply_apply x

@[simp] lemma apply_inv_apply (φ : Symmetry C) (x : C.Site) : φ (φ⁻¹ x) = x :=
  φ.toEquiv.apply_symm_apply x

/-! ### B.2. Actions on sites and lattice vectors -/

@[simp] lemma latticeAut_mul (φ ψ : Symmetry C) :
    (φ * ψ).latticeAut = ψ.latticeAut.trans φ.latticeAut := rfl

@[simp] lemma latticeAut_one : (1 : Symmetry C).latticeAut = AddEquiv.refl G := rfl

@[simp] lemma latticeAut_inv (φ : Symmetry C) : φ⁻¹.latticeAut = φ.latticeAut.symm := rfl

/-- The symmetry group acts on crystal sites by permutations. -/
instance : MulAction (Symmetry C) C.Site where
  smul φ x := φ x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[simp] lemma smul_site (φ : Symmetry C) (x : C.Site) : φ • x = φ x := rfl

/-- The symmetry group acts on lattice vectors by automorphisms of the translation group. -/
instance : DistribMulAction (Symmetry C) G where
  smul φ a := φ.latticeAut a
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero φ := map_zero φ.latticeAut
  smul_add φ := map_add φ.latticeAut

@[simp] lemma smul_vector (φ : Symmetry C) (a : G) : φ • a = φ.latticeAut a := rfl

/-! ## C. Lattice translations -/

/-- The group homomorphism sending each lattice vector to its translation symmetry. -/
def translationHom (C : Crystal G) : Multiplicative G →* Symmetry C where
  toFun a := ⟨AddAction.toPerm (Multiplicative.toAdd a), AddEquiv.refl G,
    vadd_comm (Multiplicative.toAdd a)⟩
  map_one' := ext (zero_vadd G)
  map_mul' a b := ext (add_vadd (Multiplicative.toAdd a) (Multiplicative.toAdd b))

/-- The symmetry that translates every site by the lattice vector `a`. -/
def translation (C : Crystal G) (a : G) : Symmetry C :=
  translationHom C (Multiplicative.ofAdd a)

@[simp] lemma translation_apply (a : G) (x : C.Site) : translation C a x = a +ᵥ x := rfl

@[simp] lemma latticeAut_translation (a : G) :
    (translation C a).latticeAut = AddEquiv.refl G := rfl

/-- Conjugation by `φ` maps the translation by `a` to the translation by `φ.latticeAut a`. -/
lemma conj_translation (φ : Symmetry C) (a : G) :
    φ * translation C a * φ⁻¹ = translation C (φ.latticeAut a) := by
  ext x : 1
  rw [mul_apply, mul_apply, translation_apply, map_vadd, apply_inv_apply, translation_apply]

/-- The subgroup consisting of all lattice translations. -/
def translations (C : Crystal G) : Subgroup (Symmetry C) := (translationHom C).range

instance : (translations C).Normal where
  conj_mem := by
    rintro _ ⟨a, rfl⟩ φ
    exact ⟨_, (conj_translation φ (Multiplicative.toAdd a)).symm⟩

end Symmetry

end Physlib.CondensedMatter.Crystal
