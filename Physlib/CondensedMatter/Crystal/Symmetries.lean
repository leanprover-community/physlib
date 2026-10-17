/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.CondensedMatter.Crystal.PeriodicGraph

/-!
# Symmetries of a crystal

The symmetries of a crystal respect its translations; those that also preserve the bonds form the
space group.

## i. Overview

A symmetry of a crystal permutes its sites and respects the periodicity: there is an automorphism
`A` of the translation group `G`, the linear part, such that

`φ (a +ᵥ x) = A a +ᵥ φ x`.

For `ℤᵈ`, `A` is a matrix in `GL_d(ℤ)`, a rotation or reflection of the lattice. The symmetries
form a group. The translations are the symmetries with trivial linear part, and form a normal
subgroup. Sending a symmetry to its linear part is a homomorphism whose kernel contains the
translations. The kernel is larger when the unit cell is not primitive: shifting a chain with two
sites per cell by half a cell is a symmetry with trivial linear part that is not a translation by
an element of `G`.

Bonds constrain the space group: a symmetry must preserve both the crystal's periodic structure
and its adjacency relation. Graph automorphisms alone need not preserve periodicity.

## ii. Key results

- `Crystal.Symmetry` : a symmetry of a crystal, a group.
- `Crystal.Symmetry.latticeHom` : the linear part of a symmetry, a homomorphism.
- `Crystal.Symmetry.translations` : the translations, a normal subgroup of the symmetries.
- `Crystal.PeriodicGraph.spaceGroup` : the symmetries that preserve the bonds.

## iii. Table of contents

- A. Symmetries
- B. The translations
- C. The space group of a periodic graph

## iv. References

-/

@[expose] public section

namespace Physlib.CondensedMatter.Crystal

variable {G : Type*} [AddCommGroup G] [AddGroup.FG G]

/-! ## A. Symmetries -/

/-- A symmetry of a crystal: a permutation of the sites that respects the translations, up to an
automorphism `lattice` of the translation group. -/
structure Symmetry (C : Crystal G) where
  /-- The permutation of the sites. -/
  toEquiv : C.Site ≃ C.Site
  /-- The linear part: the automorphism of the translation group. -/
  lattice : G ≃+ G
  /-- Translating a site and then mapping it is mapping it and then translating by the image. -/
  map_vadd (a : G) (x : C.Site) : toEquiv (a +ᵥ x) = lattice a +ᵥ toEquiv x

namespace Symmetry

variable {C : Crystal G}

instance : CoeFun (Symmetry C) (fun _ => C.Site → C.Site) := ⟨fun φ => φ.toEquiv⟩

/-- A symmetry is determined by its action on the sites, since translations act freely. -/
@[ext] lemma ext {φ ψ : Symmetry C} (h : ∀ x, φ x = ψ x) : φ = ψ := by
  obtain ⟨φ, A, hφ⟩ := φ
  obtain ⟨ψ, B, hψ⟩ := ψ
  obtain rfl : φ = ψ := Equiv.ext h
  obtain ⟨x₀⟩ := (inferInstance : Nonempty C.Site)
  obtain rfl : A = B := AddEquiv.ext fun a =>
    IsCancelVAdd.right_cancel _ _ (φ x₀) ((hφ a x₀).symm.trans (hψ a x₀))
  rfl

/-- Symmetries form a group under composition. -/
instance (C : Crystal G) : Group (Symmetry C) where
  mul φ ψ := ⟨ψ.toEquiv.trans φ.toEquiv, ψ.lattice.trans φ.lattice, fun a x => by
    simp [ψ.map_vadd, φ.map_vadd]⟩
  one := ⟨Equiv.refl _, AddEquiv.refl G, fun _ _ => rfl⟩
  inv φ := ⟨φ.toEquiv.symm, φ.lattice.symm, fun a x => by
    simp [Equiv.symm_apply_eq, φ.map_vadd]⟩
  mul_assoc _ _ _ := ext fun _ => rfl
  one_mul _ := ext fun _ => rfl
  mul_one _ := ext fun _ => rfl
  inv_mul_cancel φ := ext fun x => φ.toEquiv.symm_apply_apply x

/-- The product of symmetries acts by composition. -/
@[simp] lemma mul_apply (φ ψ : Symmetry C) (x : C.Site) : (φ * ψ) x = φ (ψ x) := rfl

/-- The inverse of a symmetry acts by the inverse permutation of the sites. -/
@[simp] lemma inv_apply (φ : Symmetry C) (x : C.Site) : φ⁻¹ x = φ.toEquiv.symm x := rfl

/-- The identity symmetry fixes every site. -/
@[simp] lemma one_apply (x : C.Site) : (1 : Symmetry C) x = x := rfl

/-- The linear part of a product is the composite of the linear parts. -/
@[simp] lemma lattice_mul (φ ψ : Symmetry C) : (φ * ψ).lattice = ψ.lattice.trans φ.lattice := rfl

/-- The linear part of an inverse is the inverse of the linear part. -/
@[simp] lemma lattice_inv (φ : Symmetry C) : φ⁻¹.lattice = φ.lattice.symm := rfl

/-- The identity symmetry has trivial linear part. -/
@[simp] lemma lattice_one : (1 : Symmetry C).lattice = AddEquiv.refl G := rfl

variable (C) in
/-- The permutation of the sites underlying a symmetry. -/
def toPerm : Symmetry C →* Equiv.Perm C.Site where
  toFun φ := φ.toEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

variable (C) in
/-- The linear part of a symmetry, such as a rotation or reflection of the lattice. -/
def latticeHom : Symmetry C →* Multiplicative (AddAut G) where
  toFun φ := Multiplicative.ofAdd φ.lattice
  map_one' := rfl
  map_mul' _ _ := rfl

/-! ## B. The translations -/

variable (C) in
/-- Translation by a lattice vector, as a symmetry. -/
def translation : Multiplicative G →* Symmetry C where
  toFun a := ⟨AddAction.toPerm (Multiplicative.toAdd a), AddEquiv.refl G, fun b x =>
    vadd_comm (Multiplicative.toAdd a) b x⟩
  map_one' := ext fun x => zero_vadd G x
  map_mul' a b := ext fun x => add_vadd (Multiplicative.toAdd a) (Multiplicative.toAdd b) x

/-- The translation by `a` moves a site by `a`. -/
@[simp] lemma translation_apply (a : G) (x : C.Site) :
    translation C (Multiplicative.ofAdd a) x = a +ᵥ x := rfl

variable (C) in
/-- The translations as a subgroup of the symmetries. -/
def translations : Subgroup (Symmetry C) := (translation C).range

/-- Translations have trivial linear part. -/
lemma translations_le_ker_latticeHom : translations C ≤ (latticeHom C).ker := by
  rintro _ ⟨a, rfl⟩
  rfl

/-- Conjugating a translation by a symmetry translates by the image of the vector. -/
lemma conj_translation (φ : Symmetry C) (a : G) :
    φ * translation C (Multiplicative.ofAdd a) * φ⁻¹ =
      translation C (Multiplicative.ofAdd (φ.lattice a)) :=
  ext fun x => by simp [φ.map_vadd]

/-- The translations are a normal subgroup of the symmetries. -/
instance : (translations C).Normal where
  conj_mem := by
    rintro _ ⟨a, rfl⟩ φ
    exact ⟨_, (conj_translation φ (Multiplicative.toAdd a)).symm⟩

end Symmetry

/-! ## C. The space group of a periodic graph -/

namespace PeriodicGraph

variable {C : Crystal G}

/-- The permutations of the sites that preserve adjacency in the graph. -/
def automorphisms (g : PeriodicGraph C) : Subgroup (Equiv.Perm C.Site) where
  carrier := {φ | ∀ x y, g.toSimpleGraph.Adj (φ x) (φ y) ↔ g.toSimpleGraph.Adj x y}
  one_mem' _ _ := Iff.rfl
  mul_mem' hφ hψ x y := (hφ _ _).trans (hψ x y)
  inv_mem' {φ} hφ x y := by simpa using (hφ (φ⁻¹ x) (φ⁻¹ y)).symm

/-- The space group of a periodic graph: the symmetries of its crystal that preserve the bonds. -/
def spaceGroup (g : PeriodicGraph C) : Subgroup (Symmetry C) :=
  g.automorphisms.comap (Symmetry.toPerm C)

/-- A symmetry is in the space group when it preserves adjacency. -/
lemma mem_spaceGroup_iff (g : PeriodicGraph C) {φ : Symmetry C} :
    φ ∈ g.spaceGroup ↔ ∀ x y, g.toSimpleGraph.Adj (φ x) (φ y) ↔ g.toSimpleGraph.Adj x y :=
  Iff.rfl

/-- Translations are in the space group, since they preserve the bonds. -/
lemma translations_le_spaceGroup (g : PeriodicGraph C) :
    Symmetry.translations C ≤ g.spaceGroup := by
  rintro _ ⟨a, rfl⟩ x y
  exact g.adj_vadd (Multiplicative.toAdd a) x y

end PeriodicGraph

end Physlib.CondensedMatter.Crystal
