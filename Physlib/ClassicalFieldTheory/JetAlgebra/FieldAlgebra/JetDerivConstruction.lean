/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.ClassicalFieldTheory.JetAlgebra.FieldAlgebra.JetDerivClass
public import Physlib.Relativity.IsLorentzDeriv
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Physlib.ClassicalFieldTheory.JetAlgebra.FieldAlgebra.Statistics
/-!
# The total derivative on the bosonic and fermionic algebras: constructions

## i. Overview

The construction of the formal total derivative `∂_μ` on the two concrete field algebras,
and the proof that each is a `HasJetDeriv` — after which everything in
`Physlib.ClassicalFieldTheory.JetAlgebra.FieldAlgebra.JetDeriv` applies to both.

* On the bosonic algebra it is the derivation of the symmetric algebra extending the shift
  `∂_s φ_α ↦ ∂_{s + {μ}} φ_α` of the component functions.
* On the fermionic algebra it is the *even* derivation of the exterior algebra extending the
  same shift, built through the trivial square-zero extension.

In both cases the Leibniz rule has the same form, with no Koszul signs. The file ends with
the compatibility of each total derivative with the inclusion of a species.

## ii. Key results

- `BosonicAlgebra.jetDeriv`, `FermionicAlgebra.jetDeriv` : the constructions.
- `BosonicAlgebra.instHasJetDeriv`, `FermionicAlgebra.instHasJetDeriv`.
- `BosonicAlgebra.comap_jetDeriv`, `FermionicAlgebra.comap_jetDeriv` : the inclusion of a
  species is a map of differential algebras.

-/

@[expose] public section

section Bosonic

namespace BosonicAlgebra

open TensorProduct

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-!

## A. The formal total derivative on the bosonic algebra

-/

/-- The formal total spacetime derivative on the bosonic algebra of a `V`-valued matter
  field in the direction `μ`: the derivation extending the shift
  `∂_s φ_α ↦ ∂_{s + {μ}} φ_α` of the component functions. -/
noncomputable def jetDeriv (μ : Fin 1 ⊕ Fin 3) :
    BosonicAlgebra V →ₗ[ℂ] BosonicAlgebra V :=
  SymmetricAlgebra.derivationOfLinear (JetComponentSpace.jetDeriv μ)

/-- On a component function the total derivative is the shift of the derivative label. -/
@[simp]
lemma jetDeriv_ι (μ : Fin 1 ⊕ Fin 3) (x : JetComponentSpace V) :
    jetDeriv μ (SymmetricAlgebra.ι ℂ _ x) =
      SymmetricAlgebra.ι ℂ _ (JetComponentSpace.jetDeriv μ x) :=
  SymmetricAlgebra.derivationOfLinear_ι _ x

@[simp]
lemma jetDeriv_one (μ : Fin 1 ⊕ Fin 3) : jetDeriv (V := V) μ (1 : BosonicAlgebra V) = 0 :=
  SymmetricAlgebra.derivationOfLinear_one _

@[simp]
lemma jetDeriv_algebraMap (μ : Fin 1 ⊕ Fin 3) (r : ℂ) :
    jetDeriv (V := V) μ (algebraMap ℂ (BosonicAlgebra V) r) = 0 :=
  SymmetricAlgebra.derivationOfLinear_algebraMap _ r

/-- The total derivative is a derivation: the Leibniz rule holds on the bosonic
  algebra. -/
lemma jetDeriv_mul (μ : Fin 1 ⊕ Fin 3) (x y : BosonicAlgebra V) :
    jetDeriv μ (x * y) = jetDeriv μ x * y + x * jetDeriv μ y :=
  SymmetricAlgebra.derivationOfLinear_mul _ x y

/-- The total derivative of the bosonic algebra is a total derivative in the sense of
  `HasJetDeriv`: the generic theory of `FieldAlgebra.jetDeriv` applies. -/
noncomputable instance instHasJetDeriv : HasJetDeriv V (BosonicAlgebra V) where
  jetDeriv := jetDeriv
  jetDeriv_ι := jetDeriv_ι
  jetDeriv_algebraMap := jetDeriv_algebraMap
  jetDeriv_mul := jetDeriv_mul

lemma jetDeriv_eq (μ : Fin 1 ⊕ Fin 3) :
    FieldAlgebra.jetDeriv (A := BosonicAlgebra V) μ = jetDeriv μ := rfl

/-!

## D. Compatibility with the inclusion of a species

-/

variable {W : Type} [AddCommGroup W] [Module ℂ W]

/-- **The inclusion of a species is a map of differential algebras.** Pulling back along a
  map of target spaces commutes with the total derivative: the two act on different labels
  of a component function. -/
lemma comap_jetDeriv (f : V →ₗ[ℂ] W) (μ : Fin 1 ⊕ Fin 3) (x : BosonicAlgebra W) :
    comap f (FieldAlgebra.jetDeriv μ x) = FieldAlgebra.jetDeriv μ (comap f x) := by
  induction x using FieldAlgebra.induction with
  | algebraMap r =>
    rw [FieldAlgebra.jetDeriv_algebraMap, map_zero, AlgHom.commutes,
      FieldAlgebra.jetDeriv_algebraMap]
  | ι v =>
    rw [FieldAlgebra.jetDeriv_ι, comap_ι, comap_ι, FieldAlgebra.jetDeriv_ι]
    exact congrArg (FieldAlgebra.ι _)
      (DFunLike.congr_fun (JetComponentSpace.comap_jetDeriv f μ) v)
  | mul a b ha hb => simp only [FieldAlgebra.jetDeriv_mul, map_add, map_mul, ha, hb]
  | add a b ha hb => simp only [map_add, ha, hb]

end BosonicAlgebra

end Bosonic

section Fermionic

namespace FermionicAlgebra

open TensorProduct

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-!

## A. The formal total derivative on the fermionic algebra

The formal total spacetime derivative extends from the component functions to the whole
fermionic algebra as an even derivation: `∂_μ (x y) = (∂_μ x) y + x (∂_μ y)`, with no
Koszul signs.

-/

/-- The generator map of the total derivative into the trivial square-zero extension of the
  fermionic algebra: `ι x ↦ (ι x, ι (∂_μ x))`. -/
noncomputable def jetDerivGen (μ : Fin 1 ⊕ Fin 3) :
    JetComponentSpace V →ₗ[ℂ] TrivSqZeroExt (FermionicAlgebra V) (FermionicAlgebra V) where
  toFun x := (ExteriorAlgebra.ι ℂ x,
    ExteriorAlgebra.ι ℂ (JetComponentSpace.jetDeriv μ x))
  map_add' x y := by
    simp only [map_add]
    rfl
  map_smul' c x := by
    simp only [map_smul, RingHom.id_apply]
    rfl

@[simp]
lemma jetDerivGen_fst (μ : Fin 1 ⊕ Fin 3) (x : JetComponentSpace V) :
    (jetDerivGen μ x).fst = ExteriorAlgebra.ι ℂ x := rfl

@[simp]
lemma jetDerivGen_snd (μ : Fin 1 ⊕ Fin 3) (x : JetComponentSpace V) :
    (jetDerivGen μ x).snd = ExteriorAlgebra.ι ℂ (JetComponentSpace.jetDeriv μ x) := rfl

/-- The generator map squares to zero: degree-one elements of the exterior algebra
  anticommute. -/
lemma jetDerivGen_mul_self (μ : Fin 1 ⊕ Fin 3) (x : JetComponentSpace V) :
    jetDerivGen μ x * jetDerivGen μ x = 0 := by
  refine TrivSqZeroExt.ext ?_ ?_
  · rw [TrivSqZeroExt.fst_mul, jetDerivGen_fst, ExteriorAlgebra.ι_sq_zero,
      TrivSqZeroExt.fst_zero]
  · rw [TrivSqZeroExt.snd_mul, jetDerivGen_fst, jetDerivGen_snd, TrivSqZeroExt.snd_zero,
      smul_eq_mul, op_smul_eq_mul]
    exact ExteriorAlgebra.ι_add_mul_swap x (JetComponentSpace.jetDeriv μ x)

/-- The lift of the total derivative to the trivial square-zero extension of the fermionic
  algebra: the algebra homomorphism `x ↦ (x, ∂_μ x)`. -/
noncomputable def jetDerivHom (μ : Fin 1 ⊕ Fin 3) :
    FermionicAlgebra V →ₐ[ℂ] TrivSqZeroExt (FermionicAlgebra V) (FermionicAlgebra V) :=
  ExteriorAlgebra.lift ℂ ⟨jetDerivGen μ, jetDerivGen_mul_self μ⟩

@[simp]
lemma jetDerivHom_ι (μ : Fin 1 ⊕ Fin 3) (x : JetComponentSpace V) :
    jetDerivHom μ (ExteriorAlgebra.ι ℂ x) = jetDerivGen μ x := by
  rw [jetDerivHom, ExteriorAlgebra.lift_ι_apply]

/-- The first component of the square-zero lift is the identity. -/
@[simp]
lemma jetDerivHom_fst (μ : Fin 1 ⊕ Fin 3) (x : FermionicAlgebra V) :
    (jetDerivHom μ x).fst = x := by
  have h : (TrivSqZeroExt.fstHom ℂ (FermionicAlgebra V) (FermionicAlgebra V)).comp
      (jetDerivHom μ) = AlgHom.id ℂ (FermionicAlgebra V) := by
    refine ExteriorAlgebra.hom_ext (LinearMap.ext fun v => ?_)
    simp
  exact DFunLike.congr_fun h x

/-- The formal total spacetime derivative on the fermionic algebra of a `V`-valued matter
  field in the direction `μ`: the even derivation extending the shift
  `∂_s ψ_α ↦ ∂_{s + {μ}} ψ_α` of the component functions. -/
noncomputable def jetDeriv (μ : Fin 1 ⊕ Fin 3) :
    FermionicAlgebra V →ₗ[ℂ] FermionicAlgebra V where
  toFun x := (jetDerivHom μ x).snd
  map_add' x y := congrArg TrivSqZeroExt.snd (map_add (jetDerivHom μ) x y)
  map_smul' c x := congrArg TrivSqZeroExt.snd (map_smul (jetDerivHom μ) c x)

lemma jetDeriv_apply (μ : Fin 1 ⊕ Fin 3) (x : FermionicAlgebra V) :
    jetDeriv μ x = (jetDerivHom μ x).snd := rfl

/-- On a component function the total derivative is the shift of the derivative label. -/
@[simp]
lemma jetDeriv_ι (μ : Fin 1 ⊕ Fin 3) (x : JetComponentSpace V) :
    jetDeriv μ (ExteriorAlgebra.ι ℂ x) =
      ExteriorAlgebra.ι ℂ (JetComponentSpace.jetDeriv μ x) := by
  rw [jetDeriv_apply, jetDerivHom_ι, jetDerivGen_snd]

@[simp]
lemma jetDeriv_one (μ : Fin 1 ⊕ Fin 3) : jetDeriv (V := V) μ (1 : FermionicAlgebra V) = 0 :=
  congrArg TrivSqZeroExt.snd (map_one (jetDerivHom (V := V) μ))

@[simp]
lemma jetDeriv_algebraMap (μ : Fin 1 ⊕ Fin 3) (r : ℂ) :
    jetDeriv (V := V) μ (algebraMap ℂ (FermionicAlgebra V) r) = 0 := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, jetDeriv_one, smul_zero]

/-- The total derivative is an even derivation: the Leibniz rule holds on the fermionic
  algebra with no Koszul signs. -/
lemma jetDeriv_mul (μ : Fin 1 ⊕ Fin 3) (x y : FermionicAlgebra V) :
    jetDeriv μ (x * y) = jetDeriv μ x * y + x * jetDeriv μ y := by
  have h : jetDeriv μ (x * y) =
      (jetDerivHom μ x).fst * jetDeriv μ y + jetDeriv μ x * (jetDerivHom μ y).fst :=
    congrArg TrivSqZeroExt.snd (map_mul (jetDerivHom μ) x y)
  rw [jetDerivHom_fst, jetDerivHom_fst] at h
  exact h.trans (add_comm _ _)

/-- The total derivative of the fermionic algebra is a total derivative in the sense of
  `HasJetDeriv`: the generic theory of `FieldAlgebra.jetDeriv` applies. -/
noncomputable instance instHasJetDeriv : HasJetDeriv V (FermionicAlgebra V) where
  jetDeriv := jetDeriv
  jetDeriv_ι := jetDeriv_ι
  jetDeriv_algebraMap := jetDeriv_algebraMap
  jetDeriv_mul := jetDeriv_mul

lemma jetDeriv_eq (μ : Fin 1 ⊕ Fin 3) :
    FieldAlgebra.jetDeriv (A := FermionicAlgebra V) μ = jetDeriv μ := rfl

/-!

## D. Compatibility with the inclusion of a species

-/

variable {W : Type} [AddCommGroup W] [Module ℂ W]

/-- **The inclusion of a species is a map of differential algebras.** Pulling back along a
  map of target spaces commutes with the total derivative: the two act on different labels
  of a component function. -/
lemma comap_jetDeriv (f : V →ₗ[ℂ] W) (μ : Fin 1 ⊕ Fin 3) (x : FermionicAlgebra W) :
    comap f (FieldAlgebra.jetDeriv μ x) = FieldAlgebra.jetDeriv μ (comap f x) := by
  induction x using FieldAlgebra.induction with
  | algebraMap r =>
    rw [FieldAlgebra.jetDeriv_algebraMap, map_zero, AlgHom.commutes,
      FieldAlgebra.jetDeriv_algebraMap]
  | ι v =>
    rw [FieldAlgebra.jetDeriv_ι, comap_ι, comap_ι, FieldAlgebra.jetDeriv_ι]
    exact congrArg (FieldAlgebra.ι _)
      (DFunLike.congr_fun (JetComponentSpace.comap_jetDeriv f μ) v)
  | mul a b ha hb => simp only [FieldAlgebra.jetDeriv_mul, map_add, map_mul, ha, hb]
  | add a b ha hb => simp only [map_add, ha, hb]

end FermionicAlgebra

end Fermionic
