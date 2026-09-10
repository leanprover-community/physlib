/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.Matter.BosonicAlgebra.JetDeriv
/-!
# The Lorentz action on the bosonic algebra

## i. Overview

Given a representation of `SL(2,ℂ)` on the target space `V` of a bosonic matter field, the
Lorentz group acts on the bosonic algebra by the symmetric-algebra functor applied to its
action on the jet component space. On a component function `∂_s φ_α` the derivative labels
transform by the Lorentz matrix and the target index contragrediently by `V`.

The formal total derivative is a Lorentz vector for this action, which is exactly the
content of the class `Lorentz.IsLorentzDeriv`; the instance is registered here, so all the
boost-weight machinery of `Physlib.Relativity.IsLorentzDeriv` applies to the bosonic
algebra of any matter field.

## ii. Key results

- `BosonicAlgebra.repLorentzGroup` : the Lorentz action on the bosonic algebra.
- `BosonicAlgebra.repLorentzGroupAlgHom` : the action as an algebra homomorphism.
- `BosonicAlgebra.repLorentzGroup_ofField` : `ofField` is `SL(2,ℂ)`-equivariant.
- `BosonicAlgebra.repLorentzGroup_jetDeriv` : the total derivative is a Lorentz vector.
- `BosonicAlgebra.instIsLorentzDeriv` : the resulting `Lorentz.IsLorentzDeriv` instance.

## iii. Table of contents

- A. The action of the Lorentz group
  - A.1. Equivariance of the field and its conjugate
- B. Lorentz covariance of the total derivative

-/

@[expose] public section

namespace StandardModel

namespace BosonicAlgebra

open Matrix MatrixGroups TensorProduct

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-!

## A. The action of the Lorentz group

-/

/-- **The Lorentz action on the bosonic algebra** of a `V`-valued matter field, induced
  from a representation `repV` of `SL(2,ℂ)` on `V`: the symmetric-algebra functor applied
  to the Lorentz action on the jet component space. -/
noncomputable def repLorentzGroup (repV : Representation ℂ SL(2,ℂ) V) :
    Representation ℂ SL(2,ℂ) (BosonicAlgebra V) where
  toFun Λ := (SymmetricAlgebra.map (JetComponentSpace.repLorentzGroup repV Λ)).toLinearMap
  map_one' := by
    simp only [map_one, Module.End.one_eq_id, SymmetricAlgebra.map_id, AlgHom.toLinearMap_id]
  map_mul' Λ₁ Λ₂ := by
    simp only [map_mul, Module.End.mul_eq_comp, ← SymmetricAlgebra.map_comp_map,
      AlgHom.comp_toLinearMap]

lemma repLorentzGroup_apply (repV : Representation ℂ SL(2,ℂ) V) (Λ : SL(2,ℂ))
    (x : BosonicAlgebra V) :
    repLorentzGroup repV Λ x =
      SymmetricAlgebra.map (JetComponentSpace.repLorentzGroup repV Λ) x := rfl

@[simp]
lemma repLorentzGroup_apply_one (repV : Representation ℂ SL(2,ℂ) V) (Λ : SL(2,ℂ)) :
    repLorentzGroup repV Λ (1 : BosonicAlgebra V) = 1 := by
  simp [repLorentzGroup_apply]

lemma repLorentzGroup_apply_mul (repV : Representation ℂ SL(2,ℂ) V) (Λ : SL(2,ℂ))
    (x y : BosonicAlgebra V) :
    repLorentzGroup repV Λ (x * y)
      = repLorentzGroup repV Λ x * repLorentzGroup repV Λ y := by
  simp [repLorentzGroup_apply]

/-- On a component function the Lorentz action is the action on the component space. -/
@[simp]
lemma repLorentzGroup_ι (repV : Representation ℂ SL(2,ℂ) V) (Λ : SL(2,ℂ))
    (v : JetComponentSpace V) :
    repLorentzGroup repV Λ (SymmetricAlgebra.ι ℂ _ v) =
      SymmetricAlgebra.ι ℂ _ (JetComponentSpace.repLorentzGroup repV Λ v) := by
  rw [repLorentzGroup_apply, SymmetricAlgebra.map_apply_ι]

/-- The Lorentz action as an algebra homomorphism: it preserves the symmetric product, so a
  Lorentz transformation acts on a Lagrangian term factor by factor. -/
noncomputable def repLorentzGroupAlgHom (repV : Representation ℂ SL(2,ℂ) V) (Λ : SL(2,ℂ)) :
    BosonicAlgebra V →ₐ[ℂ] BosonicAlgebra V where
  toFun := repLorentzGroup repV Λ
  map_add' := LinearMap.map_add _
  map_zero' := LinearMap.map_zero _
  map_one' := repLorentzGroup_apply_one repV Λ
  map_mul' := repLorentzGroup_apply_mul repV Λ
  commutes' r := by simp [repLorentzGroup_apply]

/-!

### A.1. Equivariance of the field and its conjugate

-/

/-- **`ofField` is `SL(2,ℂ)`-equivariant.** The undifferentiated component functions carry
  the contragredient of the representation on the target space, and no derivative labels
  are generated: `ofField` intertwines `repV.dual` with the action on the bosonic
  algebra. -/
@[simp]
lemma repLorentzGroup_ofField (repV : Representation ℂ SL(2,ℂ) V) (Λ : SL(2,ℂ))
    (φ : Module.Dual ℂ V) :
    repLorentzGroup repV Λ (ofField φ) = ofField (repV.dual Λ φ) := by
  rw [ofField_apply, repLorentzGroup_ι, ofField_apply]
  congr 1
  refine Prod.ext ?_ ?_
  · rw [JetComponentSpace.repLorentzGroup_fst_tmul,
      DerivAlgebraComplex.repLorentzGroup_apply_one]
    rfl
  · rw [JetComponentSpace.repLorentzGroup_snd]
    exact map_zero _

/-- **`ofConjField` is `SL(2,ℂ)`-equivariant**, for the conjugate of the representation on
  the target space: the conjugate component functions transform by `star` of the spinor
  matrix. -/
@[simp]
lemma repLorentzGroup_ofConjField (repV : Representation ℂ SL(2,ℂ) V) (Λ : SL(2,ℂ))
    (φ : Module.Dual ℂ (ConjModule V)) :
    repLorentzGroup repV Λ (ofConjField φ) = ofConjField (repV.conj.dual Λ φ) := by
  rw [ofConjField_apply, repLorentzGroup_ι, ofConjField_apply]
  congr 1
  refine Prod.ext ?_ ?_
  · rw [JetComponentSpace.repLorentzGroup_fst]
    exact map_zero _
  · rw [JetComponentSpace.repLorentzGroup_snd]
    show (DerivAlgebraComplex.repLorentzGroup Λ 1) ⊗ₜ[ℂ] (repV.conj.dual Λ φ) = _
    rw [DerivAlgebraComplex.repLorentzGroup_apply_one]

/-!

## B. Lorentz covariance of the total derivative

-/

set_option maxHeartbeats 4000000 in
/-- **The total derivative on the bosonic algebra is a Lorentz vector.** The four
  derivations `∂_μ` transform into each other by the columns of the Lorentz matrix of `Λ`,
  exactly as the covector index `μ` should. -/
lemma repLorentzGroup_jetDeriv (repV : Representation ℂ SL(2,ℂ) V) (Λ : SL(2,ℂ))
    (μ : Fin 1 ⊕ Fin 3) (x : BosonicAlgebra V) :
    repLorentzGroup repV Λ (jetDeriv μ x) =
      ∑ a, (((Lorentz.SL2C.toLorentzGroup Λ).1 a μ : ℝ) : ℂ) •
        jetDeriv a (repLorentzGroup repV Λ x) := by
  induction x using SymmetricAlgebra.induction with
  | algebraMap r =>
    rw [jetDeriv_algebraMap, map_zero]
    refine (Finset.sum_eq_zero fun a _ => ?_).symm
    rw [Algebra.algebraMap_eq_smul_one, map_smul, repLorentzGroup_apply_one, map_smul,
      jetDeriv_one, smul_zero, smul_zero]
  | ι v =>
    rw [jetDeriv_ι, repLorentzGroup_ι, repLorentzGroup_ι,
      JetComponentSpace.repLorentzGroup_jetDeriv, map_sum]
    exact Finset.sum_congr rfl fun a _ => by rw [map_smul, jetDeriv_ι]
  | mul a b ha hb =>
    rw [jetDeriv_mul, map_add, repLorentzGroup_apply_mul, repLorentzGroup_apply_mul, ha, hb,
      Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib, repLorentzGroup_apply_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [jetDeriv_mul, smul_add, smul_mul_assoc, mul_smul_comm]
  | add a b ha hb =>
    rw [map_add, map_add, map_add, ha, hb, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => by rw [map_add, smul_add]

/-- The total derivatives on the bosonic algebra form a Lorentz derivative, giving access
  to the boost-weight machinery of `Physlib.Relativity.IsLorentzDeriv`. -/
instance instIsLorentzDeriv (repV : Representation ℂ SL(2,ℂ) V) :
    Lorentz.IsLorentzDeriv (repLorentzGroup repV) (jetDeriv (V := V)) where
  rep_deriv := repLorentzGroup_jetDeriv repV _ _ _

end BosonicAlgebra

end StandardModel
