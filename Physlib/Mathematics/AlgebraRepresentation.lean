/-
Copyright (c) 2026 Nathaneal Sajan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaneal Sajan
-/
module

public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
/-!
# Representations acting by algebra maps

## i. Overview

A representation of a monoid on an algebra need not respect the multiplication; the ones
that do are the ones a field theory uses, and this file collects the two constructions on
them that are otherwise missing.

Section A is about `Representation.tprod` on a tensor product of two algebras. The unit and
the product of `A ⊗[k] B` are given by those of the factors, so a pair of unit-preserving
or multiplicative representations gives one on the tensor product. The lemmas are stated at
abstract types with the factor laws as hypotheses, which is what lets them be applied at a
large concrete algebra without unfolding it: neither the unit nor the product of a free
algebra presented as a quotient can be reduced cheaply.

Section B restricts a representation to a subalgebra it preserves. The invariance
hypothesis is stated pointwise, in the form the ambient invariance lemmas produce.

Section C restricts the scalars of a representation: a representation on a complex vector
space is in particular a representation on the underlying real vector space.

Section E bundles an algebra map together with equivariance for two independently supplied
pairs of representations of two monoids, the two target representations being multiplicative
on the whole target: `Representation.EquivariantAlgHom`. Nothing relates the two pairs, the
target actions are not assumed to commute, and they are not assumed unital, which over a
monoid does not follow from multiplicativity. Section F base changes such a map along an
extension of scalars, in both directions, and section G records the one affine identity an
algebra map is used for when a representation acts on generators by a shift.

## ii. Key results

- `Representation.tprod_apply_one`, `Representation.tprod_apply_one_tmul`,
  `Representation.tprod_apply_tmul_one` : the unit laws on a tensor product.
- `Representation.tprod_apply_mul` : multiplicativity on a tensor product.
- `Representation.restrictSubalgebra` : the restriction to an invariant subalgebra, with
  `Representation.inclusion_restrictSubalgebra` for two nested ones.
- `Representation.restrictScalars` : the restriction of scalars.
- `Representation.toAlgHom` : a multiplicative representation of a group as algebra maps.
- `Representation.EquivariantAlgHom` : an algebra map intertwining two pairs of
  representations, with `EquivariantAlgHom.id`, `EquivariantAlgHom.comp`,
  `EquivariantAlgHom.compEquiv`, `EquivariantAlgHom.restrictSubalgebra` and
  `EquivariantAlgHom.compFst`.
- `Representation.baseChange` : the base change of a representation, with
  `Representation.baseChange_naturality`.
- `Representation.liftEquiv_baseChange` : base change preserves equivariance, and
  `Representation.EquivariantAlgHom.liftEquivBaseChange` : equivariant maps out of a base
  change are the equivariant maps over the smaller ring.
- `AlgHom.map_add_smul_one` : an algebra map on an affine combination `x + z • 1`.

## iii. Table of contents

- A. Tensor products of multiplicative representations
- B. Restriction to an invariant subalgebra
- C. Restriction of scalars
- D. Multiplicative representations as algebra maps
- E. Equivariant algebra maps
- F. Base change of an equivariant algebra map
- G. Affine combinations under an algebra map

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
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x₁ x₂ h₁ h₂ => rw [add_mul, map_add, map_add, h₁, h₂, add_mul]
  | tmul a₁ b₁ =>
    induction y using TensorProduct.induction_on with
    | zero => simp
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

@[simp]
lemma coe_restrictSubalgebra {k A G : Type*} [CommSemiring k]
    [Monoid G] [Semiring A] [Algebra k A] (ρ : Representation k G A) (S : Subalgebra k A)
    (hS : ∀ (g : G) {x : A}, x ∈ S → ρ g x ∈ S) (g : G) (x : S) :
    (ρ.restrictSubalgebra S hS g x : A) = ρ g (x : A) := rfl

/-- The restrictions to two nested invariant subalgebras agree along the inclusion of the
  smaller into the larger. -/
lemma inclusion_restrictSubalgebra {k A G : Type*} [CommSemiring k]
    [Monoid G] [Semiring A] [Algebra k A] (ρ : Representation k G A) {S S' : Subalgebra k A}
    (h : S ≤ S') (hS : ∀ (g : G) {x : A}, x ∈ S → ρ g x ∈ S)
    (hS' : ∀ (g : G) {x : A}, x ∈ S' → ρ g x ∈ S') (g : G) (x : S) :
    Subalgebra.inclusion h (ρ.restrictSubalgebra S hS g x)
      = ρ.restrictSubalgebra S' hS' g (Subalgebra.inclusion h x) := rfl

/-!

## C. Restriction of scalars

-/

/-- The restriction of scalars of a representation: a representation on an `S`-module is a
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
    rw [← Module.End.mul_apply, ← map_mul ρ, mul_inv_cancel, map_one, Module.End.one_apply]
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
  on the whole of `B`. The two pairs are independent: the actions of `G₁` and `G₂` are not
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

/-- Precomposition with an algebra equivalence of the sources intertwining the source
  representations: equivariant maps out of equivalent sources correspond. -/
noncomputable def compEquiv {A' : Type*} [Semiring A'] [Algebra k A']
    {ρ₁' : Representation k G₁ A'} {ρ₂' : Representation k G₂ A'} (e : A' ≃ₐ[k] A)
    (he₁ : ∀ (g : G₁) (x : A'), e (ρ₁' g x) = ρ₁ g (e x))
    (he₂ : ∀ (g : G₂) (x : A'), e (ρ₂' g x) = ρ₂ g (e x)) :
    EquivariantAlgHom ρ₁ σ₁ ρ₂ σ₂ ≃ EquivariantAlgHom ρ₁' σ₁ ρ₂' σ₂ where
  toFun f := f.comp e.toAlgHom he₁ he₂
  invFun f := f.comp e.symm.toAlgHom
    (fun g x => e.injective (by
      simp only [AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply, he₁]))
    (fun g x => e.injective (by
      simp only [AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply, he₂]))
  left_inv f :=
    EquivariantAlgHom.ext (AlgHom.ext fun x => congrArg f.toAlgHom (e.apply_symm_apply x))
  right_inv f :=
    EquivariantAlgHom.ext (AlgHom.ext fun x => congrArg f.toAlgHom (e.symm_apply_apply x))

@[simp]
lemma compEquiv_toAlgHom {A' : Type*} [Semiring A'] [Algebra k A']
    {ρ₁' : Representation k G₁ A'} {ρ₂' : Representation k G₂ A'} (e : A' ≃ₐ[k] A)
    (he₁ : ∀ (g : G₁) (x : A'), e (ρ₁' g x) = ρ₁ g (e x))
    (he₂ : ∀ (g : G₂) (x : A'), e (ρ₂' g x) = ρ₂ g (e x))
    (f : EquivariantAlgHom ρ₁ σ₁ ρ₂ σ₂) :
    (compEquiv e he₁ he₂ f).toAlgHom = f.toAlgHom.comp e.toAlgHom := rfl

@[simp]
lemma compEquiv_symm_toAlgHom {A' : Type*} [Semiring A'] [Algebra k A']
    {ρ₁' : Representation k G₁ A'} {ρ₂' : Representation k G₂ A'} (e : A' ≃ₐ[k] A)
    (he₁ : ∀ (g : G₁) (x : A'), e (ρ₁' g x) = ρ₁ g (e x))
    (he₂ : ∀ (g : G₂) (x : A'), e (ρ₂' g x) = ρ₂ g (e x))
    (f : EquivariantAlgHom ρ₁' σ₁ ρ₂' σ₂) :
    ((compEquiv e he₁ he₂).symm f).toAlgHom = f.toAlgHom.comp e.symm.toAlgHom := rfl

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

/-!

## F. Base change of an equivariant algebra map

-/

/-- Base change along `R → S` preserves equivariance: the `S`-algebra map out of `S ⊗[R] A`
  corresponding to an equivariant `R`-algebra map `f` intertwines the base change of the
  source action with the target action. -/
lemma liftEquiv_baseChange {R S A B G : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
    [Semiring A] [Algebra R A] [Semiring B] [Algebra S B] [Algebra R B] [IsScalarTower R S B]
    [Monoid G] (f : A →ₐ[R] B) (ρ : Representation R G A) (σ : Representation S G B)
    (hf : ∀ (g : G) (x : A), f (ρ g x) = σ g (f x)) (g : G) (x : S ⊗[R] A) :
    AlgHom.liftEquiv R S A B f (LinearMap.baseChange S (ρ g) x)
      = σ g (AlgHom.liftEquiv R S A B f x) := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | tmul z a =>
    rw [LinearMap.baseChange_tmul, AlgHom.liftEquiv_tmul, AlgHom.liftEquiv_tmul,
      map_smul (σ g), hf]

/-- The base change of a representation along `R → S`: the same action on the second factor
  of `S ⊗[R] M`. -/
noncomputable def baseChange {R M G : Type*} [CommSemiring R] (S : Type*) [CommSemiring S]
    [Algebra R S] [AddCommMonoid M] [Module R M] [Monoid G] (ρ : Representation R G M) :
    Representation S G (S ⊗[R] M) where
  toFun g := LinearMap.baseChange S (ρ g)
  map_one' := by
    rw [map_one, Module.End.one_eq_id, LinearMap.baseChange_id, Module.End.one_eq_id]
  map_mul' g₁ g₂ := by
    rw [map_mul, Module.End.mul_eq_comp, LinearMap.baseChange_comp, Module.End.mul_eq_comp]

@[simp]
lemma baseChange_tmul {R M G : Type*} [CommSemiring R] (S : Type*) [CommSemiring S]
    [Algebra R S] [AddCommMonoid M] [Module R M] [Monoid G] (ρ : Representation R G M) (g : G)
    (s : S) (x : M) : baseChange S ρ g (s ⊗ₜ[R] x) = s ⊗ₜ[R] ρ g x := rfl

/-- Base change is natural: a linear map intertwining two representations base changes to
  one intertwining their base changes. -/
lemma baseChange_naturality {R M N G : Type*} [CommSemiring R] (S : Type*) [CommSemiring S]
    [Algebra R S] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N] [Monoid G]
    {ρ : Representation R G M} {σ : Representation R G N} (f : M →ₗ[R] N)
    (h : ∀ (g : G) (x : M), f (ρ g x) = σ g (f x)) (g : G) (y : S ⊗[R] M) :
    LinearMap.baseChange S f (baseChange S ρ g y)
      = baseChange S σ g (LinearMap.baseChange S f y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => rw [map_add, map_add, hu, hv, map_add, map_add]
  | tmul s x =>
    rw [LinearMap.baseChange_tmul, baseChange_tmul, baseChange_tmul, LinearMap.baseChange_tmul, h]

/-- A representation on a base change acting on the pure tensors through a representation on
  the second factor is that representation's base change. -/
lemma eq_baseChange_of_tmul {R S A G : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
    [AddCommMonoid A] [Module R A] [Monoid G] (ρ : Representation R G A)
    (ρ' : Representation S G (S ⊗[R] A))
    (h : ∀ (g : G) (s : S) (x : A), ρ' g (s ⊗ₜ[R] x) = s ⊗ₜ[R] ρ g x) (g : G) (y : S ⊗[R] A) :
    ρ' g y = LinearMap.baseChange S (ρ g) y := by
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add u v hu hv => rw [map_add, map_add, hu, hv]
  | tmul s x => rw [h, LinearMap.baseChange_tmul]

/-- For a target over `S`, the equivariant `R`-algebra maps out of `A` are the equivariant
  `S`-algebra maps out of the base change `S ⊗[R] A`, by `AlgHom.liftEquiv`. The two source
  actions on the base change are recognised by their values on the pure tensors, and the
  target keeps its `S`-actions, restricted to `R` on the left-hand side. -/
noncomputable def EquivariantAlgHom.liftEquivBaseChange {R S A B G₁ G₂ : Type*} [CommSemiring R]
    [CommSemiring S] [Algebra R S] [Semiring A] [Algebra R A] [Semiring B] [Algebra S B]
    [Algebra R B] [IsScalarTower R S B] [Monoid G₁] [Monoid G₂]
    {ρ₁ : Representation R G₁ A} {ρ₂ : Representation R G₂ A}
    {ρ₁' : Representation S G₁ (S ⊗[R] A)} {ρ₂' : Representation S G₂ (S ⊗[R] A)}
    {σ₁ : Representation S G₁ B} {σ₂ : Representation S G₂ B}
    (h₁ : ∀ (g : G₁) (s : S) (x : A), ρ₁' g (s ⊗ₜ[R] x) = s ⊗ₜ[R] ρ₁ g x)
    (h₂ : ∀ (g : G₂) (s : S) (x : A), ρ₂' g (s ⊗ₜ[R] x) = s ⊗ₜ[R] ρ₂ g x) :
    EquivariantAlgHom ρ₁ (σ₁.restrictScalars R) ρ₂ (σ₂.restrictScalars R)
      ≃ EquivariantAlgHom ρ₁' σ₁ ρ₂' σ₂ where
  toFun f :=
    { toAlgHom := AlgHom.liftEquiv R S A B f.toAlgHom
      map_fst := fun g y => by
        rw [eq_baseChange_of_tmul ρ₁ ρ₁' h₁]
        exact liftEquiv_baseChange f.toAlgHom ρ₁ σ₁ f.map_fst g y
      map_snd := fun g y => by
        rw [eq_baseChange_of_tmul ρ₂ ρ₂' h₂]
        exact liftEquiv_baseChange f.toAlgHom ρ₂ σ₂ f.map_snd g y
      fst_mul := f.fst_mul
      snd_mul := f.snd_mul }
  invFun F :=
    { toAlgHom := (AlgHom.liftEquiv R S A B).symm F.toAlgHom
      map_fst := fun g x => by
        show F.toAlgHom ((1 : S) ⊗ₜ[R] ρ₁ g x) = σ₁ g (F.toAlgHom ((1 : S) ⊗ₜ[R] x))
        rw [← h₁, F.map_fst]
      map_snd := fun g x => by
        show F.toAlgHom ((1 : S) ⊗ₜ[R] ρ₂ g x) = σ₂ g (F.toAlgHom ((1 : S) ⊗ₜ[R] x))
        rw [← h₂, F.map_snd]
      fst_mul := F.fst_mul
      snd_mul := F.snd_mul }
  left_inv f := EquivariantAlgHom.ext ((AlgHom.liftEquiv R S A B).symm_apply_apply f.toAlgHom)
  right_inv F := EquivariantAlgHom.ext ((AlgHom.liftEquiv R S A B).apply_symm_apply F.toAlgHom)

end Representation

/-!

## G. Affine combinations under an algebra map

-/

/-- An algebra map carries an affine combination `x + z • 1` to the same combination of the
  image, the shift being the image of a scalar. -/
lemma AlgHom.map_add_smul_one {k A B : Type*} [CommSemiring k] [Semiring A] [Algebra k A]
    [Semiring B] [Algebra k B] (f : A →ₐ[k] B) (x : A) (z : k) :
    f (x + z • (1 : A)) = f x + z • (1 : B) := by
  rw [← Algebra.algebraMap_eq_smul_one, map_add, AlgHom.commutes,
    Algebra.algebraMap_eq_smul_one]
