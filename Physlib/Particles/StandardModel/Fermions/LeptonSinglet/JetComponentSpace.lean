/-
Copyright (c) 2026 Nathaneal Sajan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaneal Sajan
-/
module

public import Physlib.Particles.StandardModel.Fermions.LeptonSinglet.Basic
public import Physlib.Particles.StandardModel.GaugeGroup.Jet.Basic
public import Physlib.Particles.LagrangianTheory.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
/-!
# The jet component space of the charged-lepton singlet

## i. Overview

A Lagrangian containing a charged-lepton singlet may have terms of the form
`∂_μ ∂_ν ψ`. These expressions are component functions taking a section of the
bundle of charged-lepton singlets and returning a complex number. The space of
all such component functions is the jet component space of the charged-lepton
singlet.

The jet gauge group and the Lorentz group act on this space, and it carries the
formal total spacetime derivative and the mass-weight scaling.

## ii. Key results

- `JetGenerators` : the generators `∂_s ψ_α` and `∂_s ψ̄_α` of the component space.
- `JetComponentSpace` : the space of component functions.
- `JetComponentSpace.repLorentzGroup` : the Lorentz action.
- `JetComponentSpace.repJetGaugeGroupI` : the jet gauge action.
- `JetComponentSpace.jetDeriv` : the formal total spacetime derivative.
- `JetComponentSpace.massWeightScale` : the mass-weight scaling.

## iii. Table of contents

- A. The jet component vector space
  - A.1. The action of the jet gauge group
- B. The formal total derivative on the component functions
- C. The mass-weight scaling on the component functions
- D. The total derivative on the summands of the component space

-/

@[expose] public section

namespace StandardModel

namespace LeptonSinglet

open Matrix MatrixGroups

/-!

## A. The jet component vector space

A Lagrangian containing a charged lepton singlet may have terms
of the form `∂_μ ∂_ν ψ`. These expressions should be considered as
component functions which takes in a section of the
bundle of charged lepton singlets and returns a complex number.

The space of all such component functions is what we call the jet component space.
The lagrangian is an element of the algebra over all such component
functions for all the fields in the theory.

For matter particles, the (jet) Gauge group acts on the
jet component space as a representation. This is not case for the gauge bosons.

-/

open TensorProduct LagrangianTheory

inductive JetGenerators where
  | dψ (s : Multiset (Fin 1 ⊕ Fin 3)) (α : Fin 2) : JetGenerators
  | dbarψ (s : Multiset (Fin 1 ⊕ Fin 3)) (α : Fin 2) : JetGenerators
deriving DecidableEq

def JetGenerators.equiv : JetGenerators ≃
    (Multiset (Fin 1 ⊕ Fin 3) × Fin 2 ⊕ Multiset (Fin 1 ⊕ Fin 3) × Fin 2) where
  toFun
    | JetGenerators.dψ s α => Sum.inl (s, α)
    | JetGenerators.dbarψ s α => Sum.inr (s, α)
  invFun
    | Sum.inl (s, α) => JetGenerators.dψ s α
    | Sum.inr (s, α) => JetGenerators.dbarψ s α
  left_inv := by
    intro x
    cases x <;> rfl
  right_inv := by
    intro x
    cases x <;> rfl

def JetGenerators.massWeight : JetGenerators → ℕ
  | JetGenerators.dψ s _ => 3 + 2 * s.card
  | JetGenerators.dbarψ s _ => 3 + 2 * s.card

abbrev JetComponentSpace :=
  (SymmetricAlgebra ℂ (Module.Dual ℂ Lorentz.CoℂModule) ⊗[ℂ]
    Module.Dual ℂ LeptonSinglet) ×
  (SymmetricAlgebra ℂ (Module.Dual ℂ Lorentz.CoℂModule) ⊗[ℂ]
    Module.Dual ℂ (ConjModule LeptonSinglet))

noncomputable def JetComponentSpace.basis : Module.Basis JetGenerators ℂ JetComponentSpace :=
  ((DerivAlgebraComplex.basis.tensorProduct
      LeptonSinglet.basis.dualBasis).prod
    (DerivAlgebraComplex.basis.tensorProduct
      (LeptonSinglet.basis.conj.dualBasis))).reindex JetGenerators.equiv.symm

/-- The basis vector of the jet component space at the zeroth-order singlet
  generator: the unit of the dual jet algebra tensored with the dual basis of the
  singlet, in the first (unconjugated) factor. -/
lemma JetComponentSpace.basis_dψ_nil (α : Fin 2) :
    JetComponentSpace.basis (.dψ {} α) =
      ((1 : SymmetricAlgebra ℂ (Module.Dual ℂ Lorentz.CoℂModule)) ⊗ₜ[ℂ]
        LeptonSinglet.basis.dualBasis α, 0) := by
  rw [JetComponentSpace.basis, Module.Basis.reindex_apply,
    show JetGenerators.equiv.symm.symm (.dψ {} α) = Sum.inl ({}, α) from rfl]
  refine Prod.ext ?_ ?_
  · rw [Module.Basis.prod_apply_inl_fst, Module.Basis.tensorProduct_apply',
      DerivAlgebraComplex.basis_nil]
  · rw [Module.Basis.prod_apply_inl_snd]

/-- The basis vector of the jet component space at a first-order singlet
  generator: the dual derivative symbol tensored with the dual basis of the
  singlet, in the first (unconjugated) factor. -/
lemma JetComponentSpace.basis_dψ_singleton (μ : Fin 1 ⊕ Fin 3) (α : Fin 2) :
    JetComponentSpace.basis (.dψ {μ} α) =
      (SymmetricAlgebra.ι ℂ (Module.Dual ℂ Lorentz.CoℂModule)
        (Lorentz.complexCoBasis.dualBasis μ) ⊗ₜ[ℂ]
        LeptonSinglet.basis.dualBasis α, 0) := by
  rw [JetComponentSpace.basis, Module.Basis.reindex_apply,
    show JetGenerators.equiv.symm.symm (.dψ {μ} α) = Sum.inl ({μ}, α) from rfl]
  refine Prod.ext ?_ ?_
  · rw [Module.Basis.prod_apply_inl_fst, Module.Basis.tensorProduct_apply',
      DerivAlgebraComplex.basis_singleton]
  · rw [Module.Basis.prod_apply_inl_snd]

/-- The basis vector of the jet component space at a general singlet generator:
  the dual jet algebra basis vector at its multiset of derivative indices,
  tensored with the dual basis of the singlet, in the first (unconjugated)
  factor. -/
lemma JetComponentSpace.basis_dψ (s : Multiset (Fin 1 ⊕ Fin 3)) (α : Fin 2) :
    JetComponentSpace.basis (.dψ s α) =
      (DerivAlgebraComplex.basis s ⊗ₜ[ℂ] LeptonSinglet.basis.dualBasis α, 0) := by
  rw [JetComponentSpace.basis, Module.Basis.reindex_apply,
    show JetGenerators.equiv.symm.symm (.dψ s α) = Sum.inl (s, α) from rfl]
  refine Prod.ext ?_ ?_
  · rw [Module.Basis.prod_apply_inl_fst, Module.Basis.tensorProduct_apply']
  · rw [Module.Basis.prod_apply_inl_snd]

/-- The basis vector of the jet component space at a general conjugate-singlet
  generator: the dual jet algebra basis vector at its multiset of derivative
  indices, tensored with the conjugate dual basis of the singlet, in the second
  (conjugated) factor. -/
lemma JetComponentSpace.basis_dbarψ (s : Multiset (Fin 1 ⊕ Fin 3)) (α : Fin 2) :
    JetComponentSpace.basis (.dbarψ s α) =
      (0, DerivAlgebraComplex.basis s ⊗ₜ[ℂ] LeptonSinglet.basis.conj.dualBasis α) := by
  rw [JetComponentSpace.basis, Module.Basis.reindex_apply,
    show JetGenerators.equiv.symm.symm (.dbarψ s α) = Sum.inr (s, α) from rfl]
  refine Prod.ext ?_ ?_
  · rw [Module.Basis.prod_apply_inr_fst]
  · rw [Module.Basis.prod_apply_inr_snd, Module.Basis.tensorProduct_apply']

noncomputable def JetComponentSpace.repLorentzGroup :
    Representation ℂ (SL(2,ℂ)) JetComponentSpace :=
  (DerivAlgebraComplex.repLorentzGroup.tprod LeptonSinglet.repLorentzGroup.dual).prod
  (DerivAlgebraComplex.repLorentzGroup.tprod LeptonSinglet.repLorentzGroup.conj.dual)

/-- The Lorentz action on the zeroth-order lepton jet coordinate: the
  contragredient conjugate spinor action. -/
lemma JetComponentSpace.repLorentzGroup_basis_dψ_nil (Λ : SL(2,ℂ)) (α : Fin 2) :
    JetComponentSpace.repLorentzGroup Λ (JetComponentSpace.basis (.dψ {} α)) =
      ∑ β, star ((Λ⁻¹).1 α β) • JetComponentSpace.basis (.dψ {} β) := by
  rw [basis_dψ_nil,
    show JetComponentSpace.repLorentzGroup Λ =
      LinearMap.prodMap
        (TensorProduct.map (DerivAlgebraComplex.repLorentzGroup Λ)
          (LeptonSinglet.repLorentzGroup.dual Λ))
        (TensorProduct.map (DerivAlgebraComplex.repLorentzGroup Λ)
          (LeptonSinglet.repLorentzGroup.conj.dual Λ)) from rfl,
    LinearMap.prodMap_apply, map_zero, TensorProduct.map_tmul,
    DerivAlgebraComplex.repLorentzGroup_apply_one,
    LeptonSinglet.repLorentzGroup_dual_dualBasis, TensorProduct.tmul_sum]
  have hb : ∀ β : Fin 2, JetComponentSpace.basis
      (.dψ (0 : Multiset (Fin 1 ⊕ Fin 3)) β) =
      ((1 : SymmetricAlgebra ℂ (Module.Dual ℂ Lorentz.CoℂModule)) ⊗ₜ[ℂ]
        LeptonSinglet.basis.dualBasis β, 0) := fun β => basis_dψ_nil β
  refine Prod.ext ?_ ?_
  · simp [Prod.fst_sum, hb, TensorProduct.tmul_smul]
  · simp [Prod.snd_sum, hb]

set_option maxHeartbeats 1000000 in
/-- The Lorentz action on the first-order lepton jet coordinate: the derivative
  slot transforms by the columns of the Lorentz matrix and the spinor slot
  contragrediently. -/
lemma JetComponentSpace.repLorentzGroup_basis_dψ_singleton (Λ : SL(2,ℂ))
    (μ : Fin 1 ⊕ Fin 3) (α : Fin 2) :
    JetComponentSpace.repLorentzGroup Λ (JetComponentSpace.basis (.dψ {μ} α)) =
      ∑ ν, ∑ β, ((((Lorentz.SL2C.toLorentzGroup Λ).1 ν μ : ℝ) : ℂ) *
        star ((Λ⁻¹).1 α β)) • JetComponentSpace.basis (.dψ {ν} β) := by
  rw [basis_dψ_singleton,
    show JetComponentSpace.repLorentzGroup Λ =
      LinearMap.prodMap
        (TensorProduct.map (DerivAlgebraComplex.repLorentzGroup Λ)
          (LeptonSinglet.repLorentzGroup.dual Λ))
        (TensorProduct.map (DerivAlgebraComplex.repLorentzGroup Λ)
          (LeptonSinglet.repLorentzGroup.conj.dual Λ)) from rfl,
    LinearMap.prodMap_apply, map_zero, TensorProduct.map_tmul,
    DerivAlgebraComplex.repLorentzGroup_apply_ι,
    Lorentz.CoℂModule.SL2CRep_dual_dualBasis,
    LeptonSinglet.repLorentzGroup_dual_dualBasis, map_sum, TensorProduct.sum_tmul]
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_sum, Prod.smul_fst, basis_dψ_singleton, map_smul,
      TensorProduct.smul_tmul', TensorProduct.tmul_sum, TensorProduct.sum_tmul,
      Finset.smul_sum, TensorProduct.tmul_smul, smul_smul]
    refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun β _ => ?_
    rw [mul_comm]
  · simp [Prod.snd_sum, basis_dψ_singleton, TensorProduct.tmul_sum,
      TensorProduct.sum_tmul, map_smul, TensorProduct.smul_tmul']

/-- The Lorentz action on the zeroth-order conjugate lepton jet coordinate. -/
lemma JetComponentSpace.repLorentzGroup_basis_dbarψ_nil (Λ : SL(2,ℂ)) (α : Fin 2) :
    JetComponentSpace.repLorentzGroup Λ (JetComponentSpace.basis (.dbarψ {} α)) =
      ∑ β, (Λ⁻¹).1 α β • JetComponentSpace.basis (.dbarψ {} β) := by
  rw [basis_dbarψ,
    show JetComponentSpace.repLorentzGroup Λ =
      LinearMap.prodMap
        (TensorProduct.map (DerivAlgebraComplex.repLorentzGroup Λ)
          (LeptonSinglet.repLorentzGroup.dual Λ))
        (TensorProduct.map (DerivAlgebraComplex.repLorentzGroup Λ)
          (LeptonSinglet.repLorentzGroup.conj.dual Λ)) from rfl,
    LinearMap.prodMap_apply, map_zero, TensorProduct.map_tmul,
    show DerivAlgebraComplex.basis ({} : Multiset (Fin 1 ⊕ Fin 3)) = 1 from
      DerivAlgebraComplex.basis_nil,
    DerivAlgebraComplex.repLorentzGroup_apply_one,
    LeptonSinglet.repLorentzGroup_conj_dual_dualBasis, TensorProduct.tmul_sum]
  have hb0 : DerivAlgebraComplex.basis (0 : Multiset (Fin 1 ⊕ Fin 3)) = 1 :=
    DerivAlgebraComplex.basis_nil
  refine Prod.ext ?_ ?_
  · simp [Prod.fst_sum, basis_dbarψ]
  · simp [Prod.snd_sum, basis_dbarψ, TensorProduct.tmul_smul, hb0]

set_option maxHeartbeats 1000000 in
/-- The Lorentz action on the first-order conjugate lepton jet coordinate. -/
lemma JetComponentSpace.repLorentzGroup_basis_dbarψ_singleton (Λ : SL(2,ℂ))
    (μ : Fin 1 ⊕ Fin 3) (α : Fin 2) :
    JetComponentSpace.repLorentzGroup Λ (JetComponentSpace.basis (.dbarψ {μ} α)) =
      ∑ ν, ∑ β, ((((Lorentz.SL2C.toLorentzGroup Λ).1 ν μ : ℝ) : ℂ) *
        (Λ⁻¹).1 α β) • JetComponentSpace.basis (.dbarψ {ν} β) := by
  rw [basis_dbarψ,
    show JetComponentSpace.repLorentzGroup Λ =
      LinearMap.prodMap
        (TensorProduct.map (DerivAlgebraComplex.repLorentzGroup Λ)
          (LeptonSinglet.repLorentzGroup.dual Λ))
        (TensorProduct.map (DerivAlgebraComplex.repLorentzGroup Λ)
          (LeptonSinglet.repLorentzGroup.conj.dual Λ)) from rfl,
    LinearMap.prodMap_apply, map_zero, TensorProduct.map_tmul,
    show DerivAlgebraComplex.basis ({μ} : Multiset (Fin 1 ⊕ Fin 3)) =
        SymmetricAlgebra.ι ℂ (Module.Dual ℂ Lorentz.CoℂModule)
          (Lorentz.complexCoBasis.dualBasis μ) from
      DerivAlgebraComplex.basis_singleton μ,
    DerivAlgebraComplex.repLorentzGroup_apply_ι,
    Lorentz.CoℂModule.SL2CRep_dual_dualBasis,
    LeptonSinglet.repLorentzGroup_conj_dual_dualBasis, map_sum,
    TensorProduct.sum_tmul]
  refine Prod.ext ?_ ?_
  · simp [Prod.fst_sum, basis_dbarψ, TensorProduct.tmul_sum,
      TensorProduct.sum_tmul, map_smul, TensorProduct.smul_tmul']
  · simp only [Prod.snd_sum, Prod.smul_snd, basis_dbarψ,
      DerivAlgebraComplex.basis_singleton, map_smul, TensorProduct.smul_tmul',
      TensorProduct.tmul_sum, TensorProduct.sum_tmul, Finset.smul_sum,
      TensorProduct.tmul_smul, smul_smul]
    refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun β _ => ?_
    rw [mul_comm]

/-!


### A.1. The action of the jet gauge group

Under the action of the gauge group
`∂_s ψ` transforms as
`∑ (x + y = s), ∂_x (star u ^ 6) ∂_y ψ`, and similarly for the conjugate.


-/
/-- The action of the jet gauge group on the dual jet algebra of the
  charged-lepton singlet's component functions. Component functions transform
  contragrediently to the field, so the hypercharge power series is
  `u ^ 6 = (star u ^ 6)⁻¹`, acting through the Leibniz rule on the dual
  derivative symbols. -/
noncomputable def dualJetAlgebraRepJetGaugeGroupI :
    Representation ℂ JetGaugeGroupI DerivAlgebraComplex where
  toFun U := DerivAlgebraComplex.jetRingAction (((U.2.2 : unitary JetRing) : JetRing) ^ 6)
  map_one' := by
    rw [show (((1 : JetGaugeGroupI).2.2 : unitary JetRing) : JetRing) ^ 6 =
        (1 : JetRing) by simp, DerivAlgebraComplex.jetRingAction_one]
    rfl
  map_mul' U₁ U₂ := by
    rw [show (((U₁ * U₂ : JetGaugeGroupI).2.2 : unitary JetRing) : JetRing) ^ 6 =
        ((U₁.2.2 : unitary JetRing) : JetRing) ^ 6 *
          ((U₂.2.2 : unitary JetRing) : JetRing) ^ 6 by
      rw [show (((U₁ * U₂ : JetGaugeGroupI).2.2 : unitary JetRing) : JetRing) =
          ((U₁.2.2 : unitary JetRing) : JetRing) * ((U₂.2.2 : unitary JetRing) : JetRing)
          from rfl, mul_pow],
      DerivAlgebraComplex.jetRingAction_mul, Module.End.mul_eq_comp]

/-- The action of the jet gauge group on the dual jet algebra of the conjugate
  charged-lepton singlet's component functions: the conjugate components
  transform with the conjugate-contragredient hypercharge power series
  `star u ^ 6`. -/
noncomputable def dualJetAlgebraRepJetGaugeGroupIConj :
    Representation ℂ JetGaugeGroupI
      (SymmetricAlgebra ℂ (Module.Dual ℂ Lorentz.CoℂModule)) where
  toFun U := DerivAlgebraComplex.jetRingAction ((star ((U.2.2 : unitary JetRing) : JetRing)) ^ 6)
  map_one' := by
    rw [show (star (((1 : JetGaugeGroupI).2.2 : unitary JetRing) : JetRing)) ^ 6 =
        (1 : JetRing) by simp, DerivAlgebraComplex.jetRingAction_one]
    rfl
  map_mul' U₁ U₂ := by
    rw [show (star (((U₁ * U₂ : JetGaugeGroupI).2.2 : unitary JetRing) : JetRing)) ^ 6 =
        (star ((U₁.2.2 : unitary JetRing) : JetRing)) ^ 6 *
          (star ((U₂.2.2 : unitary JetRing) : JetRing)) ^ 6 by
      rw [show (((U₁ * U₂ : JetGaugeGroupI).2.2 : unitary JetRing) : JetRing) =
          ((U₁.2.2 : unitary JetRing) : JetRing) * ((U₂.2.2 : unitary JetRing) : JetRing)
          from rfl, star_mul', mul_pow],
      DerivAlgebraComplex.jetRingAction_mul, Module.End.mul_eq_comp]

@[simp]
lemma dualJetAlgebraRepJetGaugeGroupI_apply (U : JetGaugeGroupI) :
    dualJetAlgebraRepJetGaugeGroupI U =
      DerivAlgebraComplex.jetRingAction (((U.2.2 : unitary JetRing) : JetRing) ^ 6) := rfl

@[simp]
lemma dualJetAlgebraRepJetGaugeGroupIConj_apply (U : JetGaugeGroupI) :
    dualJetAlgebraRepJetGaugeGroupIConj U =
      DerivAlgebraComplex.jetRingAction ((star ((U.2.2 : unitary JetRing) : JetRing)) ^ 6) := rfl

/-- The `(1, 1)_{-6}` action of the jet gauge group on the space of component
  functions of the charged-lepton singlet, its conjugate, and their derivative
  coordinates. The conventions are contragredient, matching the `.dual` and
  `.conj.dual` conventions of the global component-space representations: the
  singlet components transform through the derivative action of `u ^ 6`, the
  conjugate components through the derivative action of `star u ^ 6`, and the
  target factors are inert. On jets of constant gauge transformations the
  derivative symbols are inert and the action reduces to the dual global gauge
  action. -/
noncomputable def JetComponentSpace.repJetGaugeGroupI :
    Representation ℂ JetGaugeGroupI JetComponentSpace :=
  (dualJetAlgebraRepJetGaugeGroupI.tprod
      (Representation.trivial ℂ JetGaugeGroupI (Module.Dual ℂ LeptonSinglet))).prod
    (dualJetAlgebraRepJetGaugeGroupIConj.tprod
      (Representation.trivial ℂ JetGaugeGroupI (Module.Dual ℂ (ConjModule LeptonSinglet))))

/-- The jet gauge action preserves the unconjugated half of the component space,
  acting there by the dual derivative action of the contragredient hypercharge
  power series on the derivative symbols. -/
lemma JetComponentSpace.repJetGaugeGroupI_inl (U : JetGaugeGroupI)
    (a : SymmetricAlgebra ℂ (Module.Dual ℂ Lorentz.CoℂModule))
    (φ : Module.Dual ℂ LeptonSinglet) :
    JetComponentSpace.repJetGaugeGroupI U ((a ⊗ₜ[ℂ] φ, 0) : JetComponentSpace) =
      ((DerivAlgebraComplex.jetRingAction (((U.2.2 : unitary JetRing) : JetRing) ^ 6) a) ⊗ₜ[ℂ] φ, 0) := by
  refine Prod.ext ?_ ?_ <;>
    simp [JetComponentSpace.repJetGaugeGroupI, Representation.prod_apply_apply,
      Representation.tprod_apply, dualJetAlgebraRepJetGaugeGroupI_apply]

/-- The jet gauge action on a general element of the unconjugated half of the
  component space. -/
lemma JetComponentSpace.repJetGaugeGroupI_inl' (U : JetGaugeGroupI)
    (y : SymmetricAlgebra ℂ (Module.Dual ℂ Lorentz.CoℂModule) ⊗[ℂ]
      Module.Dual ℂ LeptonSinglet) :
    JetComponentSpace.repJetGaugeGroupI U ((y, 0) : JetComponentSpace) =
      ((TensorProduct.map (DerivAlgebraComplex.jetRingAction (((U.2.2 : unitary JetRing) : JetRing) ^ 6))
        LinearMap.id) y, 0) := by
  induction y using TensorProduct.induction_on with
  | zero =>
    rw [show ((0, 0) : JetComponentSpace) = 0 from rfl, map_zero, map_zero]
    rfl
  | add a b ha hb =>
    have hpair : ((a + b, 0) : JetComponentSpace) = (a, 0) + (b, 0) := by
      simp
    rw [hpair, map_add, ha, hb, map_add]
    simp
  | tmul a φ =>
    rw [JetComponentSpace.repJetGaugeGroupI_inl, TensorProduct.map_tmul]
    rfl

/-- The jet gauge action preserves the conjugated half of the component space,
  acting there by the dual derivative action of the conjugate-contragredient
  hypercharge power series on the derivative symbols. -/
lemma JetComponentSpace.repJetGaugeGroupI_inr (U : JetGaugeGroupI)
    (a : SymmetricAlgebra ℂ (Module.Dual ℂ Lorentz.CoℂModule))
    (φ : Module.Dual ℂ (ConjModule LeptonSinglet)) :
    JetComponentSpace.repJetGaugeGroupI U ((0, a ⊗ₜ[ℂ] φ) : JetComponentSpace) =
      (0, (DerivAlgebraComplex.jetRingAction
        ((star ((U.2.2 : unitary JetRing) : JetRing)) ^ 6) a) ⊗ₜ[ℂ] φ) := by
  refine Prod.ext ?_ ?_ <;>
    simp [JetComponentSpace.repJetGaugeGroupI, Representation.prod_apply_apply,
      Representation.tprod_apply, dualJetAlgebraRepJetGaugeGroupIConj_apply]

/-- The jet gauge action on a general element of the conjugated half of the
  component space. -/
lemma JetComponentSpace.repJetGaugeGroupI_inr' (U : JetGaugeGroupI)
    (y : SymmetricAlgebra ℂ (Module.Dual ℂ Lorentz.CoℂModule) ⊗[ℂ]
      Module.Dual ℂ (ConjModule LeptonSinglet)) :
    JetComponentSpace.repJetGaugeGroupI U ((0, y) : JetComponentSpace) =
      (0, (TensorProduct.map (DerivAlgebraComplex.jetRingAction
        ((star ((U.2.2 : unitary JetRing) : JetRing)) ^ 6)) LinearMap.id) y) := by
  induction y using TensorProduct.induction_on with
  | zero =>
    rw [show ((0, 0) : JetComponentSpace) = 0 from rfl, map_zero, map_zero]
    rfl
  | add a b ha hb =>
    have hpair : ((0, a + b) : JetComponentSpace) = (0, a) + (0, b) := by
      simp
    rw [hpair, map_add, ha, hb, map_add]
    simp
  | tmul a φ =>
    rw [JetComponentSpace.repJetGaugeGroupI_inr, TensorProduct.map_tmul]
    rfl

open MvPowerSeries in
/-- The gauge action on a lepton jet coordinate is the Leibniz expansion of
  `∂_t (u⁶ ψ)`: a sum over the splittings `t = x + y` of the `x`-th Taylor
  coefficient of the hypercharge character `u⁶` against the `y`-th coordinate.
  The weight `∏ descFactorial` together with `coeff x χ = (∂_x χ)(0) / x!`
  makes up the multi-index binomial coefficient `(t choose x)`. -/
lemma JetComponentSpace.repJetGaugeGroupI_basis_dψ (U : JetGaugeGroupI)
      (t : Multiset (Fin 1 ⊕ Fin 3)) (α : Fin 2) :
    repJetGaugeGroupI U (basis (.dψ t α)) =
      ∑ p ∈ Finset.antidiagonal t.toFinsupp,
          ((∏ μ, (t.toFinsupp μ).descFactorial (p.1 μ) : ℕ) : ℂ) •
          coeff p.1 (((U.2.2 : unitary JetRing) : JetRing) ^ 6) •
            basis (.dψ (Multiset.toFinsupp.symm p.2) α) := by
  have hb : ∀ p : (Fin 1 ⊕ Fin 3) →₀ ℕ,
      JetComponentSpace.basis (.dψ (Multiset.toFinsupp.symm p) α) =
        ((Lorentz.complexCoBasis.dualBasis.symmetricAlgebra p ⊗ₜ[ℂ]
          LeptonSinglet.basis.dualBasis α), 0) := by
    intro p
    rw [JetComponentSpace.basis_dψ, DerivAlgebraComplex.basis_apply,
      AddEquiv.apply_symm_apply]
  rw [JetComponentSpace.basis_dψ, JetComponentSpace.repJetGaugeGroupI_inl,
    DerivAlgebraComplex.basis_apply, DerivAlgebraComplex.jetRingAction_basis,
    TensorProduct.sum_tmul,
    show ∀ v : SymmetricAlgebra ℂ (Module.Dual ℂ Lorentz.CoℂModule) ⊗[ℂ]
        Module.Dual ℂ LeptonSinglet,
        ((v, 0) : JetComponentSpace) = LinearMap.inl ℂ _ _ v from fun _ => rfl,
    map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [hb p.2, ← TensorProduct.smul_tmul', ← TensorProduct.smul_tmul',
    map_smul, map_smul]
  rfl

open MvPowerSeries in
/-- The gauge action on the first-order lepton coordinate: the character at the
  base point acts on the coordinate itself, and its first Taylor coefficient
  feeds into the zeroth-order coordinate. This is the `t = {μ}` case of
  `repJetGaugeGroupI_basis_dψ`. -/
lemma JetComponentSpace.repJetGaugeGroupI_basis_dψ_singleton (U : JetGaugeGroupI)
    (μ : Fin 1 ⊕ Fin 3) (α : Fin 2) :
    repJetGaugeGroupI U (basis (.dψ {μ} α)) =
      constantCoeff (((U.2.2 : unitary JetRing) : JetRing) ^ 6) •
          basis (.dψ {μ} α) +
        coeff (Finsupp.single μ 1) (((U.2.2 : unitary JetRing) : JetRing) ^ 6) •
          basis (.dψ {} α) := by
  classical
  have hm : ({μ} : Multiset (Fin 1 ⊕ Fin 3)).toFinsupp = Finsupp.single μ 1 := by
    simp
  rw [JetComponentSpace.repJetGaugeGroupI_basis_dψ, hm, Finsupp.antidiagonal_single,
    show Finset.antidiagonal (1 : ℕ) = {(0, 1), (1, 0)} from by decide,
    Finset.map_insert, Finset.map_singleton,
    Finset.sum_insert (by simp [Finsupp.single_eq_zero]), Finset.sum_singleton]
  simp only [Function.Embedding.coe_prodMap, Function.Embedding.coeFn_mk,
    Prod.map_apply, Finsupp.single_zero, coeff_zero_eq_constantCoeff,
    Nat.descFactorial_zero, Finset.prod_const_one, Nat.cast_one, one_smul,
    Nat.descFactorial_self]
  have hw1 : (∏ x, ((Finsupp.single μ 1 : (Fin 1 ⊕ Fin 3) →₀ ℕ) x).descFactorial
      ((0 : (Fin 1 ⊕ Fin 3) →₀ ℕ) x) : ℕ) = 1 := by simp
  have hw2 : (∏ x, ((Finsupp.single μ 1 : (Fin 1 ⊕ Fin 3) →₀ ℕ) x).factorial : ℕ)
      = 1 := by
    refine Finset.prod_eq_one fun x _ => ?_
    rcases eq_or_ne μ x with rfl | h
    · simp
    · simp only [Finsupp.single_apply, if_neg h, Nat.factorial_zero]
  have htf1 : Multiset.toFinsupp.symm (Finsupp.single μ 1) =
      ({μ} : Multiset (Fin 1 ⊕ Fin 3)) := by
    rw [← hm, AddEquiv.symm_apply_apply]
  have htf0 : Multiset.toFinsupp.symm (0 : (Fin 1 ⊕ Fin 3) →₀ ℕ) =
      (0 : Multiset (Fin 1 ⊕ Fin 3)) := map_zero _
  rw [hw1, hw2, htf1, htf0]
  simp

/-!

## B. The formal total derivative on the component functions

The formal total spacetime derivative `∂_μ` acts on the component functions of
the charged-lepton jet by appending the derivative index,
`∂_s ψ_α ↦ ∂_{s + {μ}} ψ_α`, and likewise on the conjugate components.

-/

namespace JetGenerators

/-- The jet generator with one further derivative in the direction `μ`. -/
def shift (μ : Fin 1 ⊕ Fin 3) : JetGenerators → JetGenerators
  | dψ s α => dψ (s + {μ}) α
  | dbarψ s α => dbarψ (s + {μ}) α

@[simp]
lemma shift_dψ (μ : Fin 1 ⊕ Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3)) (α : Fin 2) :
    shift μ (dψ s α) = dψ (s + {μ}) α := rfl

@[simp]
lemma shift_dbarψ (μ : Fin 1 ⊕ Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3)) (α : Fin 2) :
    shift μ (dbarψ s α) = dbarψ (s + {μ}) α := rfl

/-- Appending a derivative index raises the mass weight by two: a derivative has
  mass dimension one. -/
@[simp]
lemma massWeight_shift (μ : Fin 1 ⊕ Fin 3) (j : JetGenerators) :
    (shift μ j).massWeight = j.massWeight + 2 := by
  cases j <;> simp [shift, massWeight] <;> omega

end JetGenerators

/-- The formal total spacetime derivative on the space of component functions of
  the charged-lepton singlet in the direction `μ`: the shift
  `∂_s ψ_α ↦ ∂_{s + {μ}} ψ_α` of the derivative multi-index, and likewise on the
  conjugate components. -/
noncomputable def JetComponentSpace.jetDeriv (μ : Fin 1 ⊕ Fin 3) :
    JetComponentSpace →ₗ[ℂ] JetComponentSpace :=
  JetComponentSpace.basis.constr ℂ fun j =>
    JetComponentSpace.basis (JetGenerators.shift μ j)

@[simp]
lemma JetComponentSpace.jetDeriv_basis (μ : Fin 1 ⊕ Fin 3) (j : JetGenerators) :
    JetComponentSpace.jetDeriv μ (JetComponentSpace.basis j) =
      JetComponentSpace.basis (JetGenerators.shift μ j) := by
  rw [JetComponentSpace.jetDeriv, Module.Basis.constr_basis]

lemma JetComponentSpace.jetDeriv_comm (μ ν : Fin 1 ⊕ Fin 3) (v : JetComponentSpace) :
    JetComponentSpace.jetDeriv μ (JetComponentSpace.jetDeriv ν v) =
      JetComponentSpace.jetDeriv ν (JetComponentSpace.jetDeriv μ v) := by
  have h : JetComponentSpace.jetDeriv μ ∘ₗ JetComponentSpace.jetDeriv ν =
      JetComponentSpace.jetDeriv ν ∘ₗ JetComponentSpace.jetDeriv μ := by
    refine JetComponentSpace.basis.ext fun j => ?_
    simp  [LinearMap.coe_comp, Function.comp_apply, JetComponentSpace.jetDeriv_basis,
      JetGenerators.shift, ]
    grind
  exact DFunLike.congr_fun h v

/-- The total derivative acts on each factor of the component space as multiplication by the
  derivative symbol `∂_μ` on the dual jet algebra, leaving the spinor factor alone. -/
lemma JetComponentSpace.jetDeriv_eq_prodMap (μ : Fin 1 ⊕ Fin 3) :
    JetComponentSpace.jetDeriv μ =
      LinearMap.prodMap
        (TensorProduct.map
          (LinearMap.mulRight ℂ (DerivAlgebraComplex.basis ({μ} : Multiset (Fin 1 ⊕ Fin 3))))
          LinearMap.id)
        (TensorProduct.map
          (LinearMap.mulRight ℂ (DerivAlgebraComplex.basis ({μ} : Multiset (Fin 1 ⊕ Fin 3))))
          LinearMap.id) := by
  refine JetComponentSpace.basis.ext fun j => ?_
  match j with
  | .dψ s α =>
    rw [JetComponentSpace.jetDeriv_basis]
    show JetComponentSpace.basis (.dψ (s + {μ}) α) = _
    rw [JetComponentSpace.basis_dψ, JetComponentSpace.basis_dψ]
    refine Prod.ext ?_ ?_
    · simp only [LinearMap.prodMap_apply, TensorProduct.map_tmul, LinearMap.mulRight_apply,
        LinearMap.id_apply, DerivAlgebraComplex.basis_mul]
    · simp only [LinearMap.prodMap_apply, map_zero]
  | .dbarψ s α =>
    rw [JetComponentSpace.jetDeriv_basis]
    show JetComponentSpace.basis (.dbarψ (s + {μ}) α) = _
    rw [JetComponentSpace.basis_dbarψ, JetComponentSpace.basis_dbarψ]
    refine Prod.ext ?_ ?_
    · simp only [LinearMap.prodMap_apply, map_zero]
    · simp only [LinearMap.prodMap_apply, TensorProduct.map_tmul, LinearMap.mulRight_apply,
        LinearMap.id_apply, DerivAlgebraComplex.basis_mul]

lemma JetComponentSpace.jetDeriv_fst (μ : Fin 1 ⊕ Fin 3) (v : JetComponentSpace) :
    (JetComponentSpace.jetDeriv μ v).1 =
      TensorProduct.map
        (LinearMap.mulRight ℂ (DerivAlgebraComplex.basis ({μ} : Multiset (Fin 1 ⊕ Fin 3))))
        LinearMap.id v.1 := by
  rw [JetComponentSpace.jetDeriv_eq_prodMap]; rfl

lemma JetComponentSpace.jetDeriv_snd (μ : Fin 1 ⊕ Fin 3) (v : JetComponentSpace) :
    (JetComponentSpace.jetDeriv μ v).2 =
      TensorProduct.map
        (LinearMap.mulRight ℂ (DerivAlgebraComplex.basis ({μ} : Multiset (Fin 1 ⊕ Fin 3))))
        LinearMap.id v.2 := by
  rw [JetComponentSpace.jetDeriv_eq_prodMap]; rfl

lemma JetComponentSpace.repLorentzGroup_fst (Λ : SL(2,ℂ)) (v : JetComponentSpace) :
    (JetComponentSpace.repLorentzGroup Λ v).1 =
      (DerivAlgebraComplex.repLorentzGroup.tprod LeptonSinglet.repLorentzGroup.dual) Λ v.1 :=
  rfl

lemma JetComponentSpace.repLorentzGroup_snd (Λ : SL(2,ℂ)) (v : JetComponentSpace) :
    (JetComponentSpace.repLorentzGroup Λ v).2 =
      (DerivAlgebraComplex.repLorentzGroup.tprod
        LeptonSinglet.repLorentzGroup.conj.dual) Λ v.2 :=
  rfl

/-- The covariance of the derivative-symbol multiplication on one tensor factor of the
  component space, for an arbitrary representation on the other factor. -/
private lemma repLorentzGroup_tprod_mulRight_jetSymbol {W : Type*} [AddCommGroup W]
    [Module ℂ W] (ρ : Representation ℂ SL(2,ℂ) W) (Λ : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3)
    (w : DerivAlgebraComplex ⊗[ℂ] W) :
    (DerivAlgebraComplex.repLorentzGroup.tprod ρ) Λ
      (TensorProduct.map
        (LinearMap.mulRight ℂ (DerivAlgebraComplex.basis ({μ} : Multiset (Fin 1 ⊕ Fin 3))))
        LinearMap.id w) =
    ∑ a, (((Lorentz.SL2C.toLorentzGroup Λ).1 a μ : ℝ) : ℂ) •
      TensorProduct.map
        (LinearMap.mulRight ℂ (DerivAlgebraComplex.basis ({a} : Multiset (Fin 1 ⊕ Fin 3))))
        LinearMap.id ((DerivAlgebraComplex.repLorentzGroup.tprod ρ) Λ w) := by
  have hsym : DerivAlgebraComplex.repLorentzGroup Λ
      (DerivAlgebraComplex.basis ({μ} : Multiset (Fin 1 ⊕ Fin 3))) =
      ∑ a, (((Lorentz.SL2C.toLorentzGroup Λ).1 a μ : ℝ) : ℂ) •
        DerivAlgebraComplex.basis ({a} : Multiset (Fin 1 ⊕ Fin 3)) := by
    rw [DerivAlgebraComplex.basis_singleton, DerivAlgebraComplex.repLorentzGroup_apply_ι,
      Lorentz.CoℂModule.SL2CRep_dual_dualBasis, map_sum]
    exact Finset.sum_congr rfl fun a _ => by
      rw [map_smul, DerivAlgebraComplex.basis_singleton]
  have hrep : ∀ (q : DerivAlgebraComplex) (f : W),
      (DerivAlgebraComplex.repLorentzGroup.tprod ρ) Λ (q ⊗ₜ[ℂ] f) =
        (DerivAlgebraComplex.repLorentzGroup Λ q) ⊗ₜ[ℂ] (ρ Λ f) := fun _ _ => rfl
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
    rw [map_add, map_add, map_add, hx, hy, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => by rw [map_add, smul_add]
  | tmul q f =>
    rw [TensorProduct.map_tmul, LinearMap.mulRight_apply, LinearMap.id_apply, hrep, hrep,
      DerivAlgebraComplex.repLorentzGroup_apply_mul, hsym, Finset.mul_sum,
      TensorProduct.sum_tmul]
    exact Finset.sum_congr rfl fun a _ => by
      rw [TensorProduct.map_tmul, LinearMap.mulRight_apply, LinearMap.id_apply,
        mul_smul_comm, TensorProduct.smul_tmul']

/-- **The shift is Lorentz covariant on the component space.** Appending `∂_μ` and then acting
  is acting and then appending the transformed `∂_μ`, which is a combination of the `∂_a`. -/
lemma JetComponentSpace.repLorentzGroup_jetDeriv (Λ : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3)
    (v : JetComponentSpace) :
    JetComponentSpace.repLorentzGroup Λ (JetComponentSpace.jetDeriv μ v) =
      ∑ a, (((Lorentz.SL2C.toLorentzGroup Λ).1 a μ : ℝ) : ℂ) •
        JetComponentSpace.jetDeriv a (JetComponentSpace.repLorentzGroup Λ v) := by
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_sum, Prod.smul_fst, JetComponentSpace.repLorentzGroup_fst,
      JetComponentSpace.jetDeriv_fst]
    exact repLorentzGroup_tprod_mulRight_jetSymbol _ Λ μ v.1
  · simp only [Prod.snd_sum, Prod.smul_snd, JetComponentSpace.repLorentzGroup_snd,
      JetComponentSpace.jetDeriv_snd]
    exact repLorentzGroup_tprod_mulRight_jetSymbol _ Λ μ v.2

/-!

## C. The mass-weight scaling on the component functions

-/

/-- The mass-dimension scaling on the space of component functions of the
  charged-lepton singlet: the diagonal map multiplying each component function
  `∂_s ψ_α` by `c ^ w`, where `w` is twice its mass dimension. -/
noncomputable def JetComponentSpace.massWeightScale (c : ℂ) :
    JetComponentSpace →ₗ[ℂ] JetComponentSpace :=
  JetComponentSpace.basis.constr ℂ fun j =>
    c ^ j.massWeight • JetComponentSpace.basis j

@[simp]
lemma JetComponentSpace.massWeightScale_basis (c : ℂ) (j : JetGenerators) :
    JetComponentSpace.massWeightScale c (JetComponentSpace.basis j) =
      c ^ j.massWeight • JetComponentSpace.basis j := by
  rw [JetComponentSpace.massWeightScale, Module.Basis.constr_basis]

/-- The total derivative raises the mass weight by two on the component space:
  the scaling and the derivative commute up to `c ^ 2`. -/
lemma JetComponentSpace.massWeightScale_jetDeriv (c : ℂ) (μ : Fin 1 ⊕ Fin 3)
    (v : JetComponentSpace) :
    JetComponentSpace.massWeightScale c (JetComponentSpace.jetDeriv μ v) =
      c ^ 2 • JetComponentSpace.jetDeriv μ (JetComponentSpace.massWeightScale c v) := by
  have h : JetComponentSpace.massWeightScale c ∘ₗ JetComponentSpace.jetDeriv μ =
      c ^ 2 • (JetComponentSpace.jetDeriv μ ∘ₗ JetComponentSpace.massWeightScale c) := by
    refine JetComponentSpace.basis.ext fun j => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.smul_apply,
      JetComponentSpace.jetDeriv_basis, JetComponentSpace.massWeightScale_basis,
      map_smul, JetGenerators.massWeight_shift, smul_smul, ← pow_add]
    congr 1
    ring
  exact DFunLike.congr_fun h v

/-- The mass-dimension scaling commutes with the action of jets of constant
  gauge transformations on the component space: the constant action is diagonal
  on the generator basis, with no derivative mixing. For a non-constant jet the
  higher Taylor coefficients of `u ^ 6` strictly lower the derivative degree, so
  the action does not commute with the scaling. -/
lemma JetComponentSpace.massWeightScale_repJetGaugeGroupI_ofConstant (c : ℂ) (g : GaugeGroupI) :
    JetComponentSpace.massWeightScale c ∘ₗ
        JetComponentSpace.repJetGaugeGroupI (JetGaugeGroupI.ofConstant g) =
      JetComponentSpace.repJetGaugeGroupI (JetGaugeGroupI.ofConstant g) ∘ₗ
        JetComponentSpace.massWeightScale c := by
  have hu : ((((JetGaugeGroupI.ofConstant g).2.2 : unitary JetRing)) : JetRing) =
      MvPowerSeries.C ((g.2.2 : ℂ)) := rfl
  refine JetComponentSpace.basis.ext fun j => ?_
  cases j with
  | dψ s α =>
    have hrep : JetComponentSpace.repJetGaugeGroupI (JetGaugeGroupI.ofConstant g)
        (JetComponentSpace.basis (.dψ s α)) =
          ((g.2.2 : ℂ) ^ 6) • JetComponentSpace.basis (.dψ s α) := by
      simp only [JetComponentSpace.basis_dψ]
      rw [JetComponentSpace.repJetGaugeGroupI_inl, hu, ← map_pow,
        DerivAlgebraComplex.jetRingAction_C]
      simp [TensorProduct.smul_tmul', Prod.smul_mk]
    simp only [LinearMap.coe_comp, Function.comp_apply, hrep, map_smul,
      JetComponentSpace.massWeightScale_basis]
    exact smul_comm _ _ _
  | dbarψ s α =>
    have hrep : JetComponentSpace.repJetGaugeGroupI (JetGaugeGroupI.ofConstant g)
        (JetComponentSpace.basis (.dbarψ s α)) =
          ((star (g.2.2 : ℂ)) ^ 6) • JetComponentSpace.basis (.dbarψ s α) := by
      simp only [JetComponentSpace.basis_dbarψ]
      rw [JetComponentSpace.repJetGaugeGroupI_inr, hu, JetRing.star_C, ← map_pow,
        DerivAlgebraComplex.jetRingAction_C]
      simp [TensorProduct.smul_tmul', Prod.smul_mk]
    simp only [LinearMap.coe_comp, Function.comp_apply, hrep, map_smul,
      JetComponentSpace.massWeightScale_basis]
    exact smul_comm _ _ _

/-- The mass-dimension scaling commutes with the Lorentz action on the component
  space: the Lorentz action mixes derivative symbols and spinor components only
  within a fixed derivative degree, on which the scaling is a scalar. -/
lemma JetComponentSpace.massWeightScale_repLorentzGroup (c : ℂ) (g : SL(2,ℂ)) :
    JetComponentSpace.massWeightScale c ∘ₗ JetComponentSpace.repLorentzGroup g =
      JetComponentSpace.repLorentzGroup g ∘ₗ JetComponentSpace.massWeightScale c := by
  have hfact : JetComponentSpace.massWeightScale c =
      LinearMap.prodMap
        (TensorProduct.map (DerivAlgebraComplex.gradeScale (c ^ 2)).toLinearMap
          (c ^ 3 • LinearMap.id))
        (TensorProduct.map (DerivAlgebraComplex.gradeScale (c ^ 2)).toLinearMap
          (c ^ 3 • LinearMap.id)) := by
    refine JetComponentSpace.basis.ext fun j => ?_
    cases j with
    | dψ s α =>
      have hscal : (c : ℂ) ^ (JetGenerators.dψ s α).massWeight =
          c ^ 3 * (c ^ 2) ^ s.card := by
        show c ^ (3 + 2 * s.card) = _
        ring
      rw [JetComponentSpace.massWeightScale_basis, hscal]
      simp only [JetComponentSpace.basis_dψ, LinearMap.prodMap_apply, map_zero,
        TensorProduct.map_tmul, AlgHom.toLinearMap_apply, LinearMap.smul_apply,
        LinearMap.id_apply, DerivAlgebraComplex.gradeScale_basis,
        TensorProduct.tmul_smul, TensorProduct.smul_tmul', Prod.smul_mk, smul_smul,
        smul_zero]
    | dbarψ s α =>
      have hscal : (c : ℂ) ^ (JetGenerators.dbarψ s α).massWeight =
          c ^ 3 * (c ^ 2) ^ s.card := by
        show c ^ (3 + 2 * s.card) = _
        ring
      rw [JetComponentSpace.massWeightScale_basis, hscal]
      simp only [JetComponentSpace.basis_dbarψ, LinearMap.prodMap_apply, map_zero,
        TensorProduct.map_tmul, AlgHom.toLinearMap_apply, LinearMap.smul_apply,
        LinearMap.id_apply, DerivAlgebraComplex.gradeScale_basis,
        TensorProduct.tmul_smul, TensorProduct.smul_tmul', Prod.smul_mk, smul_smul,
        smul_zero]
  have hA : (DerivAlgebraComplex.gradeScale (c ^ 2)).toLinearMap ∘ₗ
      DerivAlgebraComplex.repLorentzGroup g =
      (DerivAlgebraComplex.repLorentzGroup g :
        DerivAlgebraComplex →ₗ[ℂ] DerivAlgebraComplex) ∘ₗ
        (DerivAlgebraComplex.gradeScale (c ^ 2)).toLinearMap :=
    LinearMap.ext fun a => DerivAlgebraComplex.gradeScale_repLorentzGroup (c ^ 2) g a
  have hB1 : (c ^ 3 • (LinearMap.id : Module.End ℂ (Module.Dual ℂ LeptonSinglet))) ∘ₗ
      LeptonSinglet.repLorentzGroup.dual g =
      LeptonSinglet.repLorentzGroup.dual g ∘ₗ (c ^ 3 • LinearMap.id) := by
    rw [LinearMap.smul_comp, LinearMap.comp_smul, LinearMap.id_comp, LinearMap.comp_id]
  have hB2 : (c ^ 3 • (LinearMap.id :
      Module.End ℂ (Module.Dual ℂ (ConjModule LeptonSinglet)))) ∘ₗ
      LeptonSinglet.repLorentzGroup.conj.dual g =
      LeptonSinglet.repLorentzGroup.conj.dual g ∘ₗ (c ^ 3 • LinearMap.id) := by
    rw [LinearMap.smul_comp, LinearMap.comp_smul, LinearMap.id_comp, LinearMap.comp_id]
  have hcomp1 : TensorProduct.map (DerivAlgebraComplex.gradeScale (c ^ 2)).toLinearMap
      (c ^ 3 • LinearMap.id) ∘ₗ
      TensorProduct.map (DerivAlgebraComplex.repLorentzGroup g)
        (LeptonSinglet.repLorentzGroup.dual g) =
      TensorProduct.map (DerivAlgebraComplex.repLorentzGroup g)
        (LeptonSinglet.repLorentzGroup.dual g) ∘ₗ
      TensorProduct.map (DerivAlgebraComplex.gradeScale (c ^ 2)).toLinearMap
        (c ^ 3 • LinearMap.id) := by
    rw [← TensorProduct.map_comp, ← TensorProduct.map_comp, hA, hB1]
  have hcomp2 : TensorProduct.map (DerivAlgebraComplex.gradeScale (c ^ 2)).toLinearMap
      (c ^ 3 • LinearMap.id) ∘ₗ
      TensorProduct.map (DerivAlgebraComplex.repLorentzGroup g)
        (LeptonSinglet.repLorentzGroup.conj.dual g) =
      TensorProduct.map (DerivAlgebraComplex.repLorentzGroup g)
        (LeptonSinglet.repLorentzGroup.conj.dual g) ∘ₗ
      TensorProduct.map (DerivAlgebraComplex.gradeScale (c ^ 2)).toLinearMap
        (c ^ 3 • LinearMap.id) := by
    rw [← TensorProduct.map_comp, ← TensorProduct.map_comp, hA, hB2]
  rw [hfact, show JetComponentSpace.repLorentzGroup g =
      LinearMap.prodMap
        (TensorProduct.map (DerivAlgebraComplex.repLorentzGroup g)
          (LeptonSinglet.repLorentzGroup.dual g))
        (TensorProduct.map (DerivAlgebraComplex.repLorentzGroup g)
          (LeptonSinglet.repLorentzGroup.conj.dual g)) from rfl]
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.prodMap_apply]
  exact Prod.ext (DFunLike.congr_fun hcomp1 x.1) (DFunLike.congr_fun hcomp2 x.2)

/-!

## D. The total derivative on the summands of the component space

-/

/-- The total derivative preserves the unconjugated half of the component space,
  acting there by the shift of dual derivative symbols. -/
lemma JetComponentSpace.jetDeriv_inl (μ : Fin 1 ⊕ Fin 3)
    (a : SymmetricAlgebra ℂ (Module.Dual ℂ Lorentz.CoℂModule))
    (φ : Module.Dual ℂ LeptonSinglet) :
    JetComponentSpace.jetDeriv μ ((a ⊗ₜ[ℂ] φ, 0) : JetComponentSpace) =
      ((DerivAlgebraComplex.deriv μ a) ⊗ₜ[ℂ] φ, 0) := by
  have h : (JetComponentSpace.jetDeriv μ) ∘ₗ (LinearMap.inl ℂ
        (SymmetricAlgebra ℂ (Module.Dual ℂ Lorentz.CoℂModule) ⊗[ℂ]
          Module.Dual ℂ LeptonSinglet)
        (SymmetricAlgebra ℂ (Module.Dual ℂ Lorentz.CoℂModule) ⊗[ℂ]
          Module.Dual ℂ (ConjModule LeptonSinglet))) =
      (LinearMap.inl ℂ _ _) ∘ₗ (TensorProduct.map (DerivAlgebraComplex.deriv μ) LinearMap.id) := by
    refine (DerivAlgebraComplex.basis.tensorProduct LeptonSinglet.basis.dualBasis).ext
      fun p => ?_
    obtain ⟨s, α⟩ := p
    rw [Module.Basis.tensorProduct_apply']
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.inl_apply,
      TensorProduct.map_tmul, LinearMap.id_coe, id_eq]
    rw [show ((DerivAlgebraComplex.basis s ⊗ₜ[ℂ] LeptonSinglet.basis.dualBasis α, 0) :
        JetComponentSpace) = JetComponentSpace.basis (.dψ s α) from
        (JetComponentSpace.basis_dψ s α).symm,
      JetComponentSpace.jetDeriv_basis, JetGenerators.shift_dψ,
      JetComponentSpace.basis_dψ, DerivAlgebraComplex.deriv_basis_multiset]
  have h1 := LinearMap.congr_fun h (a ⊗ₜ[ℂ] φ)
  simpa using h1

/-- The total derivative on a general element of the unconjugated half of the
  component space. -/
lemma JetComponentSpace.jetDeriv_inl' (μ : Fin 1 ⊕ Fin 3)
    (y : SymmetricAlgebra ℂ (Module.Dual ℂ Lorentz.CoℂModule) ⊗[ℂ]
      Module.Dual ℂ LeptonSinglet) :
    JetComponentSpace.jetDeriv μ ((y, 0) : JetComponentSpace) =
      ((TensorProduct.map (DerivAlgebraComplex.deriv μ) LinearMap.id) y, 0) := by
  induction y using TensorProduct.induction_on with
  | zero =>
    rw [show ((0, 0) : JetComponentSpace) = 0 from rfl, map_zero, map_zero]
    rfl
  | add a b ha hb =>
    have hpair : ((a + b, 0) : JetComponentSpace) = (a, 0) + (b, 0) := by
      simp
    rw [hpair, map_add, ha, hb, map_add]
    simp
  | tmul a φ =>
    rw [JetComponentSpace.jetDeriv_inl, TensorProduct.map_tmul]
    rfl

/-- The total derivative preserves the conjugated half of the component space,
  acting there by the shift of dual derivative symbols. -/
lemma JetComponentSpace.jetDeriv_inr (μ : Fin 1 ⊕ Fin 3)
    (a : SymmetricAlgebra ℂ (Module.Dual ℂ Lorentz.CoℂModule))
    (φ : Module.Dual ℂ (ConjModule LeptonSinglet)) :
    JetComponentSpace.jetDeriv μ ((0, a ⊗ₜ[ℂ] φ) : JetComponentSpace) =
      (0, (DerivAlgebraComplex.deriv μ a) ⊗ₜ[ℂ] φ) := by
  have h : (JetComponentSpace.jetDeriv μ) ∘ₗ (LinearMap.inr ℂ
        (SymmetricAlgebra ℂ (Module.Dual ℂ Lorentz.CoℂModule) ⊗[ℂ]
          Module.Dual ℂ LeptonSinglet)
        (SymmetricAlgebra ℂ (Module.Dual ℂ Lorentz.CoℂModule) ⊗[ℂ]
          Module.Dual ℂ (ConjModule LeptonSinglet))) =
      (LinearMap.inr ℂ _ _) ∘ₗ (TensorProduct.map (DerivAlgebraComplex.deriv μ)
        LinearMap.id) := by
    refine (DerivAlgebraComplex.basis.tensorProduct
      (LeptonSinglet.basis.conj.dualBasis)).ext fun p => ?_
    obtain ⟨s, α⟩ := p
    rw [Module.Basis.tensorProduct_apply']
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.inr_apply,
      TensorProduct.map_tmul, LinearMap.id_coe, id_eq]
    rw [show ((0, DerivAlgebraComplex.basis s ⊗ₜ[ℂ]
        LeptonSinglet.basis.conj.dualBasis α) : JetComponentSpace) =
        JetComponentSpace.basis (.dbarψ s α) from
        (JetComponentSpace.basis_dbarψ s α).symm,
      JetComponentSpace.jetDeriv_basis, JetGenerators.shift_dbarψ,
      JetComponentSpace.basis_dbarψ, DerivAlgebraComplex.deriv_basis_multiset]
  have h1 := LinearMap.congr_fun h (a ⊗ₜ[ℂ] φ)
  simpa using h1

/-- The total derivative on a general element of the conjugated half of the
  component space. -/
lemma JetComponentSpace.jetDeriv_inr' (μ : Fin 1 ⊕ Fin 3)
    (y : SymmetricAlgebra ℂ (Module.Dual ℂ Lorentz.CoℂModule) ⊗[ℂ]
      Module.Dual ℂ (ConjModule LeptonSinglet)) :
    JetComponentSpace.jetDeriv μ ((0, y) : JetComponentSpace) =
      (0, (TensorProduct.map (DerivAlgebraComplex.deriv μ) LinearMap.id) y) := by
  induction y using TensorProduct.induction_on with
  | zero =>
    rw [show ((0, 0) : JetComponentSpace) = 0 from rfl, map_zero, map_zero]
    rfl
  | add a b ha hb =>
    have hpair : ((0, a + b) : JetComponentSpace) = (0, a) + (0, b) := by
      simp
    rw [hpair, map_add, ha, hb, map_add]
    simp
  | tmul a φ =>
    rw [JetComponentSpace.jetDeriv_inr, TensorProduct.map_tmul]
    rfl

end LeptonSinglet

end StandardModel
