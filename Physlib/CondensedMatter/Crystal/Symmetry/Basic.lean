/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.CondensedMatter.Crystal.Bonds
public import Mathlib.GroupTheory.GroupAction.Hom

/-!
# Symmetries of a crystal

The symmetries of a crystal are the permutations of its sites that respect its translations.

## i. Overview

A crystal is a pattern that repeats. Shift the whole crystal by one lattice step and it looks
exactly the same. This translation symmetry is why momentum is conserved in a solid. It is also
why the electrons of a crystal are described by waves labelled by a wavevector.

Other operations can leave the pattern looking the same, such as turning a square lattice by a
quarter turn. This file defines the operations that keep the repetition intact: they move the
sites around and turn each lattice step into another lattice step. They form a group. The
translations are a normal subgroup of it.

Every site is a copy of a site in the reference cell, so such an operation is determined by where
it sends the reference cell. When the cell has several sites, it can move them differently. For
example, shifting a chain with two sites per cell by half a cell exchanges the two sites. It is
not a translation by a lattice step.

A symmetry also moves the bonds between sites. A bond from the label `i` to the label `j` with
displacement `δ` goes to the bond from `σ i` to `σ j` with displacement `A δ + bⱼ - bᵢ`, where `σ`
is the permutation of the labels, `A` the lattice automorphism and `bᵢ` the offset at `i`. The
symmetries that respect the bonds, the space group, are defined with the periodic graph.

## ii. Key results

- `Crystal.Symmetry` : a symmetry of a crystal, a group.
- `Crystal.Symmetry.apply_eq` : a symmetry acts on every site through the image of the reference
  cell and its lattice automorphism.
- `Crystal.Symmetry.apply_eq_components` : a symmetry sends `⟨n, i⟩` to `⟨A n + bᵢ, σ i⟩`.
- `Crystal.Symmetry.lattice_mul` : the lattice automorphism of a product is the composite.
- `Crystal.Symmetry.labelHom` : the permutation of the labels by a symmetry, a homomorphism.
- `Crystal.Symmetry.Offsets` : one lattice vector for each unit-cell label.
- `Crystal.Symmetry.offset` : the cell in which a symmetry sends the reference site of a label.
- `Crystal.Symmetry.translations` : the translations, a normal subgroup of the symmetries.
- `Crystal.Symmetry.mapBond` : the image of a bond under a symmetry, an action on the bonds.

## iii. Table of contents

- A. Symmetries
  - A.1. Action on the sites
  - A.2. Group structure
  - A.3. Permutation of the labels
  - A.4. Offsets
- B. The translations
- C. Action on bonds

## iv. References

* None.

-/

@[expose] public section

namespace Physlib.CondensedMatter.Crystal

variable {G : Type*} [AddCommGroup G] [AddGroup.FG G]

/-! ## A. Symmetries -/

/-- A symmetry of a crystal: an automorphism of the action of the translation group on the sites.
It is an automorphism `lattice` of the translation group together with a bijection of the sites
that carries the action along. -/
structure Symmetry (C : Crystal G) where
  /-- The automorphism of the translation group. -/
  lattice : G ≃+ G
  /-- The map of the sites, equivariant for `lattice`: it carries the action along. -/
  toHom : AddActionHom ⇑lattice C.Site C.Site
  /-- The map of the sites is a bijection. -/
  bijective : Function.Bijective toHom

namespace Symmetry

variable {C : Crystal G}

/-! ### A.1. Action on the sites -/

/-- Symmetries with the same action on the sites are equal, since translations act freely. -/
lemma ext' {φ ψ : Symmetry C} (h : ∀ x, φ.toHom x = ψ.toHom x) : φ = ψ := by
  obtain ⟨x₀⟩ := (inferInstance : Nonempty C.Site)
  have hA (a : G) : φ.lattice a = ψ.lattice a := by
    refine IsCancelVAdd.right_cancel _ _ (φ.toHom x₀) ?_
    rw [← map_vaddₛₗ φ.toHom, h (a +ᵥ x₀), map_vaddₛₗ ψ.toHom, h x₀]
  obtain ⟨A, f, hf⟩ := φ
  obtain ⟨B, g, hg⟩ := ψ
  obtain rfl : A = B := AddEquiv.ext hA
  obtain rfl : f = g := AddActionHom.ext h
  rfl

/-- A symmetry acts on the sites. -/
instance : FunLike (Symmetry C) C.Site C.Site where
  coe φ := φ.toHom
  coe_injective _ _ h := ext' (congrFun h)

/-- A symmetry is determined by its action on the sites. -/
@[ext] lemma ext {φ ψ : Symmetry C} (h : ∀ x, φ x = ψ x) : φ = ψ := ext' h

/-- Mapping a translated site is translating the mapped site by the image of the vector. -/
lemma map_vadd (φ : Symmetry C) (a : G) (x : C.Site) : φ (a +ᵥ x) = φ.lattice a +ᵥ φ x :=
  map_vaddₛₗ φ.toHom a x

/-- A symmetry moves the site `⟨n, i⟩` by the lattice automorphism from the image of `⟨0, i⟩`. -/
lemma apply_eq (φ : Symmetry C) (n : G) (i : C.UnitCell) :
    φ ⟨n, i⟩ = ⟨φ.lattice n + (φ (Site.ref i)).cell, (φ (Site.ref i)).label⟩ := by
  simpa [Site.vadd_def] using φ.map_vadd n (Site.ref i)

/-- A symmetry as a permutation of the sites. -/
noncomputable def toEquiv (φ : Symmetry C) : C.Site ≃ C.Site := Equiv.ofBijective φ φ.bijective

/-- Composing equivariant maps gives an equivariant map. -/
lemma comp_map_vadd (φ ψ : Symmetry C) (a : G) (x : C.Site) :
    (φ ∘ ψ) (a +ᵥ x) = (ψ.lattice.trans φ.lattice) a +ᵥ (φ ∘ ψ) x := by
  rw [Function.comp_apply, ψ.map_vadd, φ.map_vadd]
  rfl

/-- The identity is equivariant for the identity automorphism. -/
lemma id_map_vadd (a : G) (x : C.Site) : id (a +ᵥ x) = AddEquiv.refl G a +ᵥ id x := rfl

/-- The inverse of an equivariant bijection is equivariant for the inverse automorphism. -/
lemma symm_map_vadd (φ : Symmetry C) (a : G) (x : C.Site) :
    φ.toEquiv.symm (a +ᵥ x) = φ.lattice.symm a +ᵥ φ.toEquiv.symm x :=
  map_vaddₛₗ (φ.toHom.inverse' φ.toEquiv.symm φ.lattice.apply_symm_apply
    φ.toEquiv.symm_apply_apply φ.toEquiv.apply_symm_apply) a x

/-! ### A.2. Group structure -/

/-- Symmetries form a group under composition. -/
noncomputable instance (C : Crystal G) : Group (Symmetry C) where
  mul φ ψ := ⟨ψ.lattice.trans φ.lattice, ⟨φ ∘ ψ, comp_map_vadd φ ψ⟩, φ.bijective.comp ψ.bijective⟩
  one := ⟨AddEquiv.refl G, ⟨id, id_map_vadd⟩, Function.bijective_id⟩
  inv φ := ⟨φ.lattice.symm, ⟨φ.toEquiv.symm, symm_map_vadd φ⟩, φ.toEquiv.symm.bijective⟩
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl
  inv_mul_cancel φ := ext φ.toEquiv.symm_apply_apply

/-- The product of symmetries acts by composition. -/
@[simp] lemma mul_apply (φ ψ : Symmetry C) (x : C.Site) : (φ * ψ) x = φ (ψ x) := rfl

/-- The inverse of a symmetry undoes it. -/
@[simp] lemma inv_apply_apply (φ : Symmetry C) (x : C.Site) : φ⁻¹ (φ x) = x :=
  φ.toEquiv.symm_apply_apply x

/-- A symmetry undoes its inverse. -/
@[simp] lemma apply_inv_apply (φ : Symmetry C) (x : C.Site) : φ (φ⁻¹ x) = x :=
  φ.toEquiv.apply_symm_apply x

/-- The permutation of the sites underlying a symmetry. -/
noncomputable def toPerm (C : Crystal G) : Symmetry C →* Equiv.Perm C.Site where
  toFun := toEquiv
  map_one' := Equiv.ext (congrFun rfl)
  map_mul' _ _ := Equiv.ext (congrFun rfl)

/-- The lattice automorphism of a product is the composite of the lattice automorphisms. -/
@[simp] lemma lattice_mul (φ ψ : Symmetry C) : (φ * ψ).lattice = φ.lattice + ψ.lattice := rfl

/-- The identity symmetry has trivial lattice automorphism. -/
@[simp] lemma lattice_one : (1 : Symmetry C).lattice = 0 := rfl

/-! ### A.3. Permutation of the labels -/

/-- The label of the image of `⟨n, i⟩` does not depend on the cell `n`. -/
lemma label_apply (φ : Symmetry C) (n : G) (i : C.UnitCell) :
    (φ ⟨n, i⟩).label = (φ (Site.ref i)).label := by
  rw [apply_eq φ n i]

/-- A symmetry permutes the labels: it sends `i` to the label of the image of `⟨0, i⟩`. -/
instance : MulAction (Symmetry C) C.UnitCell where
  smul φ i := (φ (Site.ref i)).label
  one_smul _ := rfl
  mul_smul φ ψ i := label_apply φ (ψ (Site.ref i)).cell (ψ (Site.ref i)).label

/-- The permutation of the labels by a symmetry, as a homomorphism. -/
noncomputable def labelHom (C : Crystal G) : Symmetry C →* Equiv.Perm C.UnitCell :=
  MulAction.toPermHom (Symmetry C) C.UnitCell

/-- The label permutation of a symmetry sends `i` to the label of the image of `⟨0, i⟩`. -/
lemma labelHom_apply (φ : Symmetry C) (i : C.UnitCell) :
    labelHom C φ i = (φ (Site.ref i)).label := rfl

/-! ### A.4. Offsets -/

/-- One lattice vector for each unit-cell label. Every symmetry has such offsets, and so does every
shift. -/
abbrev Offsets (C : Crystal G) := C.UnitCell → G

/-- The offsets of a symmetry: at the label `i` the cell in which the image of the reference site of
`i` lies, as a lattice vector in `G`. -/
def offset (φ : Symmetry C) : Offsets C := fun i => (φ (Site.ref i)).cell

/-- A symmetry sends the site `⟨n, i⟩` to the cell `A n + bᵢ` with label `σ i`, where `A` is its
lattice automorphism, `σ` its label permutation and `bᵢ` its offset at `i`. -/
lemma apply_eq_components (φ : Symmetry C) (x : C.Site) :
    φ x = ⟨φ.lattice x.cell + φ.offset x.label, labelHom C φ x.label⟩ :=
  apply_eq φ x.cell x.label

/-- The cell of the image of `⟨n, i⟩` is `A n + bᵢ`. -/
lemma cell_apply (φ : Symmetry C) (x : C.Site) :
    (φ x).cell = φ.lattice x.cell + φ.offset x.label :=
  congrArg Site.cell (apply_eq_components φ x)

/-! ## B. The translations -/

/-- Translations commute, so translating is equivariant for the identity automorphism. -/
lemma vadd_map_vadd (c b : G) (x : C.Site) : c +ᵥ (b +ᵥ x) = AddEquiv.refl G b +ᵥ (c +ᵥ x) :=
  vadd_comm c b x

/-- Translation as a homomorphism, with the lattice written multiplicatively. It is only used to
form the subgroup of translations; use `translation`. -/
noncomputable def translationHom (C : Crystal G) : Multiplicative G →* Symmetry C where
  toFun a := ⟨AddEquiv.refl G, ⟨AddAction.toPerm (Multiplicative.toAdd a), vadd_map_vadd _⟩,
    (AddAction.toPerm (Multiplicative.toAdd a)).bijective⟩
  map_one' := ext (zero_vadd G)
  map_mul' a b := ext (add_vadd (Multiplicative.toAdd a) (Multiplicative.toAdd b))

/-- Translation by a lattice vector, as a symmetry. -/
noncomputable def translation (C : Crystal G) (a : G) : Symmetry C :=
  translationHom C (Multiplicative.ofAdd a)

/-- The translation by `a` moves a site by `a`. -/
@[simp] lemma translation_apply (a : G) (x : C.Site) : translation C a x = a +ᵥ x := rfl

/-- Translations add. -/
lemma translation_add (a b : G) : translation C (a + b) = translation C a * translation C b :=
  map_mul (translationHom C) (Multiplicative.ofAdd a) (Multiplicative.ofAdd b)

/-- Translation by zero is the identity. -/
lemma translation_zero : translation C 0 = 1 := map_one (translationHom C)

/-- The translations as a subgroup of the symmetries. -/
noncomputable def translations (C : Crystal G) : Subgroup (Symmetry C) :=
  (translationHom C).range

/-- Translations have trivial lattice automorphism. -/
@[simp] lemma lattice_translation (a : G) : (translation C a).lattice = 0 := rfl

/-- Conjugating a translation by a symmetry translates by the image of the vector. -/
lemma conj_translation (φ : Symmetry C) (a : G) :
    φ * translation C a * φ⁻¹ = translation C (φ.lattice a) := by
  ext x : 1
  show φ (a +ᵥ φ⁻¹ x) = φ.lattice a +ᵥ x
  rw [φ.map_vadd, apply_inv_apply]

/-- The translations are a normal subgroup of the symmetries. -/
instance : (translations C).Normal where
  conj_mem := by
    rintro _ ⟨a, rfl⟩ φ
    exact ⟨_, (conj_translation φ (Multiplicative.toAdd a)).symm⟩

/-! ## C. Action on bonds -/

section Bonds

variable (φ : Symmetry C)

/-- The image of a bond under a crystal symmetry, with displacement `A δ + bⱼ - bᵢ`. -/
noncomputable def mapBond (b : Bond C) : Bond C where
  source := labelHom C φ b.source
  target := labelHom C φ b.target
  displacement := φ.lattice b.displacement + φ.offset b.target - φ.offset b.source

/-- A symmetry maps sites connected by a bond to sites connected by its image. -/
lemma mapBond_links {b : Bond C} {x y : C.Site} (h : b.Links x y) :
    (φ.mapBond b).Links (φ x) (φ y) := by
  obtain ⟨s, t, d⟩ := b
  obtain ⟨n, i⟩ := x
  obtain ⟨m, j⟩ := y
  simp only [Bond.Links] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  exact ⟨label_apply φ n i, label_apply φ _ j, by
    simp [mapBond, cell_apply, map_add, add_assoc]⟩

/-- The image of a bond under a product is the iterated image. -/
lemma mapBond_mul (ψ : Symmetry C) (b : Bond C) :
    (φ * ψ).mapBond b = φ.mapBond (ψ.mapBond b) := by
  have hl := b.links_reference
  exact Bond.eq_of_links ((φ * ψ).mapBond_links hl) (φ.mapBond_links (ψ.mapBond_links hl))

/-- The identity symmetry fixes every bond. -/
lemma mapBond_one (b : Bond C) : (1 : Symmetry C).mapBond b = b := by
  have hl := b.links_reference
  exact Bond.eq_of_links ((1 : Symmetry C).mapBond_links hl) hl

/-- The crystal symmetries act on the bonds. -/
noncomputable instance : MulAction (Symmetry C) (Bond C) where
  smul φ b := φ.mapBond b
  one_smul := mapBond_one
  mul_smul := mapBond_mul

end Bonds

end Symmetry

end Physlib.CondensedMatter.Crystal
