/-
Copyright (c) 2026 Nathaneal Sajan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import Mathlib.RepresentationTheory.Basic
/-!
# Representations acting by algebra maps

Representations on algebras which respect the multiplication, and algebra maps between them.

## i. Overview

A representation of a monoid on an algebra need not respect the multiplication. The ones
that do are the ones a field theory uses, acting on an algebra of fields, and this file
collects the constructions on them that Mathlib does not have.

Section A is about `Representation.tprod` on a tensor product of two algebras. The unit and
the product of `A ⊗[k] B` are given by those of the factors, so a pair of unit-preserving
or multiplicative representations gives one on the tensor product. The lemmas are stated at
abstract types with the factor laws as hypotheses, which is what lets them be applied at a
large concrete algebra without unfolding it: neither the unit nor the product of a free
algebra presented as a quotient can be reduced cheaply.

Section B restricts a representation to a subalgebra it preserves. The invariance
hypothesis is stated pointwise, in the form the ambient invariance lemmas produce.

Section C restricts the scalars of a representation, so that a representation on a complex
vector space is in particular a representation on the underlying real vector space. Section D
turns a multiplicative representation of a group into one by algebra maps.

Section E bundles an algebra map together with equivariance for two independently supplied
pairs of representations of two monoids, the two target representations being multiplicative
on the whole target: `Representation.EquivariantAlgHom`. Nothing relates the two pairs, the
target actions are not assumed to commute, and they are not assumed unital, which over a
monoid does not follow from multiplicativity.

## ii. Key results

- `Representation.tprod_apply_one`, `Representation.tprod_apply_one_tmul`,
  `Representation.tprod_apply_tmul_one` : the unit laws on a tensor product.
- `Representation.tprod_apply_mul` : multiplicativity on a tensor product.
- `Representation.restrictSubalgebra` : the restriction to an invariant subalgebra.
- `Representation.restrictScalars` : the restriction of scalars.
- `Representation.toAlgHom` : a multiplicative representation of a group as algebra maps.
- `Representation.EquivariantAlgHom` : an algebra map intertwining two pairs of
  representations, with `EquivariantAlgHom.id`, `EquivariantAlgHom.comp`,
  `EquivariantAlgHom.restrictSubalgebra` and `EquivariantAlgHom.compFst`.

## iii. Table of contents

- A. Tensor products of multiplicative representations
- B. Restriction to an invariant subalgebra
- C. Restriction of scalars
- D. Multiplicative representations as algebra maps
- E. Equivariant algebra maps

## iv. References

* None.

-/

@[expose] public section

open TensorProduct

namespace Representation

/-!

## A. Tensor products of multiplicative representations

-/

/-- The tensor product of two unit-preserving representations preserves the unit. -/
lemma tprod_apply_one {k G A B : Type*} [CommSemiring k] [Monoid G]
    [Ring A] [Algebra k A] [Ring B] [Algebra k B]
    (ρ : Representation k G A) (σ : Representation k G B) (g : G)
    (hρ : ρ g 1 = 1) (hσ : σ g 1 = 1) : (ρ.tprod σ) g 1 = 1 := by
  rw [Algebra.TensorProduct.one_def, Representation.tprod_apply, TensorProduct.map_tmul,
    hρ, hσ, ← Algebra.TensorProduct.one_def]

/-- On a pure tensor whose left entry is the unit only the right factor moves. -/
lemma tprod_apply_one_tmul {k G A B : Type*} [CommSemiring k]
    [Monoid G] [Ring A] [Algebra k A] [Ring B] [Algebra k B]
    (ρ : Representation k G A) (σ : Representation k G B) (g : G)
    (hρ : ρ g 1 = 1) (y : B) :
    (ρ.tprod σ) g ((1 : A) ⊗ₜ[k] y) = (1 : A) ⊗ₜ[k] σ g y := by
  rw [Representation.tprod_apply, TensorProduct.map_tmul, hρ]

/-- On a pure tensor whose right entry is the unit only the left factor moves. -/
lemma tprod_apply_tmul_one {k G A B : Type*} [CommSemiring k]
    [Monoid G] [Ring A] [Algebra k A] [Ring B] [Algebra k B]
    (ρ : Representation k G A) (σ : Representation k G B) (g : G) (x : A)
    (hσ : σ g 1 = 1) :
    (ρ.tprod σ) g (x ⊗ₜ[k] (1 : B)) = ρ g x ⊗ₜ[k] (1 : B) := by
  rw [Representation.tprod_apply, TensorProduct.map_tmul, hσ]

/-- The tensor product of two multiplicative representations on algebras is
  multiplicative. -/
lemma tprod_apply_mul {k G A B : Type*} [CommSemiring k] [Monoid G]
    [Ring A] [Algebra k A] [Ring B] [Algebra k B]
    (ρ : Representation k G A) (σ : Representation k G B)
    (hρ : ∀ (g : G) (x y : A), ρ g (x * y) = ρ g x * ρ g y)
    (hσ : ∀ (g : G) (x y : B), σ g (x * y) = σ g x * σ g y)
    (g : G) (x y : A ⊗[k] B) :
    (ρ.tprod σ) g (x * y) = (ρ.tprod σ) g x * (ρ.tprod σ) g y := by
  induction x using TensorProduct.inductionOn with
  | add x₁ x₂ h₁ h₂ => rw [add_mul, map_add, map_add, h₁, h₂, add_mul]
  | tmul a₁ b₁ =>
    induction y using TensorProduct.inductionOn with
    | add y₁ y₂ h₁ h₂ => rw [mul_add, map_add, map_add, h₁, h₂, mul_add]
    | tmul a₂ b₂ =>
      rw [Algebra.TensorProduct.tmul_mul_tmul,
        show (ρ.tprod σ) g (a₁ ⊗ₜ[k] b₁) = ρ g a₁ ⊗ₜ[k] σ g b₁ from rfl,
        show (ρ.tprod σ) g (a₂ ⊗ₜ[k] b₂) = ρ g a₂ ⊗ₜ[k] σ g b₂ from rfl,
        show (ρ.tprod σ) g ((a₁ * a₂) ⊗ₜ[k] (b₁ * b₂))
          = ρ g (a₁ * a₂) ⊗ₜ[k] σ g (b₁ * b₂) from rfl,
        hρ, hσ, Algebra.TensorProduct.tmul_mul_tmul]

/-!

## B. Restriction to an invariant subalgebra

-/

/-- The restriction of a representation to a subalgebra each group element preserves. -/
noncomputable def restrictSubalgebra {k A G : Type*} [CommSemiring k]
    [Monoid G] [Semiring A] [Algebra k A] (ρ : Representation k G A) (S : Subalgebra k A)
    (hS : ∀ (g : G) {x : A}, x ∈ S → ρ g x ∈ S) : Representation k G S where
  toFun g :=
    { toFun := fun x => ⟨ρ g (x : A), hS g x.2⟩
      map_add' := fun _ _ => Subtype.ext (map_add _ _ _)
      map_smul' := fun _ _ => Subtype.ext (map_smul _ _ _) }
  map_one' := LinearMap.ext fun x => Subtype.ext
    (LinearMap.congr_fun (map_one ρ) (x : A))
  map_mul' g₁ g₂ := LinearMap.ext fun x => Subtype.ext
    (LinearMap.congr_fun (map_mul ρ g₁ g₂) (x : A))

/-!

## C. Restriction of scalars

-/

/-- The restriction of scalars of a representation. A representation on an `S`-module is a
  representation on the same space as an `R`-module, for `R` acting through `S`. -/
def restrictScalars (R : Type*) {S G V : Type*} [CommSemiring R] [CommSemiring S] [Monoid G]
    [AddCommMonoid V] [Module R V] [Module S V] [LinearMap.CompatibleSMul V V R S]
    (ρ : Representation S G V) : Representation R G V where
  toFun g := (ρ g).restrictScalars R
  map_one' := LinearMap.ext fun x => LinearMap.congr_fun (map_one ρ) x
  map_mul' g₁ g₂ := LinearMap.ext fun x => LinearMap.congr_fun (map_mul ρ g₁ g₂) x

@[simp]
lemma restrictScalars_apply (R : Type*) {S G V : Type*} [CommSemiring R] [CommSemiring S]
    [Monoid G] [AddCommMonoid V] [Module R V] [Module S V] [LinearMap.CompatibleSMul V V R S]
    (ρ : Representation S G V) (g : G) (x : V) : ρ.restrictScalars R g x = ρ g x := rfl

/-!

## D. Multiplicative representations as algebra maps

-/

section Multiplicative

variable {k G A : Type*} [CommSemiring k] [Group G] [Ring A] [Algebra k A]
  (ρ : Representation k G A) (hρ : ∀ (g : G) (x y : A), ρ g (x * y) = ρ g x * ρ g y)

include hρ in
/-- A representation of a group acting by multiplicative maps preserves the unit. The
  action of `g` is surjective, its inverse being the action of `g⁻¹`, so `ρ g 1` is a left
  unit on the whole algebra. -/
lemma apply_one_of_mul (g : G) : ρ g 1 = 1 := by
  have hsurj (b : A) : ρ g (ρ g⁻¹ b) = b := by
    rw [← mul_apply_eq_comp, ← map_mul ρ, mul_inv_cancel, map_one, one_apply_eq_self]
  have key (b : A) : ρ g 1 * b = b := by
    conv_lhs => rw [← hsurj b, ← hρ, one_mul]
    rw [hsurj]
  simpa using key 1

/-- A representation of a group acting by multiplicative maps acts by algebra
  endomorphisms. -/
noncomputable def toAlgHom (g : G) : A →ₐ[k] A where
  toFun := ρ g
  map_one' := apply_one_of_mul ρ hρ g
  map_mul' := hρ g
  map_zero' := map_zero (ρ g)
  map_add' := map_add (ρ g)
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one, map_smul, apply_one_of_mul ρ hρ g]

@[simp]
lemma toAlgHom_apply (g : G) (x : A) : ρ.toAlgHom hρ g x = ρ g x := rfl

end Multiplicative

/-!

## E. Equivariant algebra maps

-/

section Equivariant

variable {k : Type*} [CommSemiring k] {G₁ G₂ : Type*} [Monoid G₁] [Monoid G₂]
  {A B : Type*} [Semiring A] [Algebra k A] [Semiring B] [Algebra k B]

/-- An algebra map `A →ₐ[k] B` intertwining two pairs of representations, `ρ₁, σ₁` of the
  monoid `G₁` and `ρ₂, σ₂` of the monoid `G₂`, with both target representations multiplicative
  on the whole of `B`. The two pairs are independent. The actions of `G₁` and `G₂` are not
  assumed to commute, and no relation between them is used. Unit preservation is not a field
  and does not follow from multiplicativity over a monoid; when the acting monoid is a group
  and the target is a ring it does (`Representation.apply_one_of_mul`), and the target action
  is then by algebra endomorphisms. -/
@[ext]
structure EquivariantAlgHom (ρ₁ : Representation k G₁ A) (σ₁ : Representation k G₁ B)
    (ρ₂ : Representation k G₂ A) (σ₂ : Representation k G₂ B) where
  /-- The underlying algebra map. -/
  toAlgHom : A →ₐ[k] B
  /-- The map is equivariant for the first pair of representations. -/
  map_fst : ∀ (g : G₁) (x : A), toAlgHom (ρ₁ g x) = σ₁ g (toAlgHom x)
  /-- The map is equivariant for the second pair of representations. -/
  map_snd : ∀ (g : G₂) (x : A), toAlgHom (ρ₂ g x) = σ₂ g (toAlgHom x)
  /-- The first target action is multiplicative on the whole of `B`. -/
  fst_mul : ∀ (g : G₁) (b₁ b₂ : B), σ₁ g (b₁ * b₂) = σ₁ g b₁ * σ₁ g b₂
  /-- The second target action is multiplicative on the whole of `B`. -/
  snd_mul : ∀ (g : G₂) (b₁ b₂ : B), σ₂ g (b₁ * b₂) = σ₂ g b₁ * σ₂ g b₂

namespace EquivariantAlgHom

variable {ρ₁ : Representation k G₁ A} {σ₁ : Representation k G₁ B}
  {ρ₂ : Representation k G₂ A} {σ₂ : Representation k G₂ B}

variable (ρ₁ ρ₂) in
/-- The identity map of an algebra carrying two multiplicative representations. -/
def id (h₁ : ∀ (g : G₁) (x y : A), ρ₁ g (x * y) = ρ₁ g x * ρ₁ g y)
    (h₂ : ∀ (g : G₂) (x y : A), ρ₂ g (x * y) = ρ₂ g x * ρ₂ g y) :
    EquivariantAlgHom ρ₁ ρ₁ ρ₂ ρ₂ where
  toAlgHom := AlgHom.id k A
  map_fst _ _ := rfl
  map_snd _ _ := rfl
  fst_mul := h₁
  snd_mul := h₂

@[simp]
lemma id_toAlgHom (h₁ : ∀ (g : G₁) (x y : A), ρ₁ g (x * y) = ρ₁ g x * ρ₁ g y)
    (h₂ : ∀ (g : G₂) (x y : A), ρ₂ g (x * y) = ρ₂ g x * ρ₂ g y) :
    (EquivariantAlgHom.id ρ₁ ρ₂ h₁ h₂).toAlgHom = AlgHom.id k A := rfl

/-- The precomposition with an algebra map into the source intertwining two representations
  on its own source with the two source representations; the target and its two actions are
  unchanged. -/
def comp {A' : Type*} [Semiring A'] [Algebra k A'] {ρ₁' : Representation k G₁ A'}
    {ρ₂' : Representation k G₂ A'} (f : EquivariantAlgHom ρ₁ σ₁ ρ₂ σ₂) (φ : A' →ₐ[k] A)
    (hφ₁ : ∀ (g : G₁) (x : A'), φ (ρ₁' g x) = ρ₁ g (φ x))
    (hφ₂ : ∀ (g : G₂) (x : A'), φ (ρ₂' g x) = ρ₂ g (φ x)) :
    EquivariantAlgHom ρ₁' σ₁ ρ₂' σ₂ where
  toAlgHom := f.toAlgHom.comp φ
  map_fst g x := (congrArg f.toAlgHom (hφ₁ g x)).trans (f.map_fst g (φ x))
  map_snd g x := (congrArg f.toAlgHom (hφ₂ g x)).trans (f.map_snd g (φ x))
  fst_mul := f.fst_mul
  snd_mul := f.snd_mul

@[simp]
lemma comp_toAlgHom {A' : Type*} [Semiring A'] [Algebra k A'] {ρ₁' : Representation k G₁ A'}
    {ρ₂' : Representation k G₂ A'} (f : EquivariantAlgHom ρ₁ σ₁ ρ₂ σ₂) (φ : A' →ₐ[k] A)
    (hφ₁ : ∀ (g : G₁) (x : A'), φ (ρ₁' g x) = ρ₁ g (φ x))
    (hφ₂ : ∀ (g : G₂) (x : A'), φ (ρ₂' g x) = ρ₂ g (φ x)) :
    (f.comp φ hφ₁ hφ₂).toAlgHom = f.toAlgHom.comp φ := rfl

/-- The restriction to a subalgebra of the source preserved by both source representations,
  along its inclusion; the target and its two actions are unchanged. -/
noncomputable def restrictSubalgebra (f : EquivariantAlgHom ρ₁ σ₁ ρ₂ σ₂) (S : Subalgebra k A)
    (hS₁ : ∀ (g : G₁) {x : A}, x ∈ S → ρ₁ g x ∈ S)
    (hS₂ : ∀ (g : G₂) {x : A}, x ∈ S → ρ₂ g x ∈ S) :
    EquivariantAlgHom (ρ₁.restrictSubalgebra S hS₁) σ₁ (ρ₂.restrictSubalgebra S hS₂) σ₂ :=
  f.comp S.val (fun _ _ => rfl) (fun _ _ => rfl)

@[simp]
lemma restrictSubalgebra_toAlgHom_apply (f : EquivariantAlgHom ρ₁ σ₁ ρ₂ σ₂) (S : Subalgebra k A)
    (hS₁ : ∀ (g : G₁) {x : A}, x ∈ S → ρ₁ g x ∈ S)
    (hS₂ : ∀ (g : G₂) {x : A}, x ∈ S → ρ₂ g x ∈ S) (x : S) :
    (f.restrictSubalgebra S hS₁ hS₂).toAlgHom x = f.toAlgHom x := rfl

/-- The precomposition of the first pair of representations with a monoid map; the algebra
  map is unchanged. -/
def compFst {H : Type*} [Monoid H] (f : EquivariantAlgHom ρ₁ σ₁ ρ₂ σ₂) (φ : H →* G₁) :
    EquivariantAlgHom (ρ₁.comp φ) (σ₁.comp φ) ρ₂ σ₂ where
  toAlgHom := f.toAlgHom
  map_fst h x := f.map_fst (φ h) x
  map_snd := f.map_snd
  fst_mul h := f.fst_mul (φ h)
  snd_mul := f.snd_mul

@[simp]
lemma compFst_toAlgHom {H : Type*} [Monoid H] (f : EquivariantAlgHom ρ₁ σ₁ ρ₂ σ₂) (φ : H →* G₁) :
    (f.compFst φ).toAlgHom = f.toAlgHom := rfl

end EquivariantAlgHom

end Equivariant

end Representation
