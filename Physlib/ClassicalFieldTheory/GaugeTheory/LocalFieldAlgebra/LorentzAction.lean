/-
Copyright (c) 2026 Nathaneal Sajan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaneal Sajan
-/
module

public import Physlib.ClassicalFieldTheory.GaugeTheory.LocalFieldAlgebra.Basic
public import Physlib.ClassicalFieldTheory.GaugeTheory.GaugeBoson.LocalGaugeFieldAlgebra.LorentzAction
/-!
# The Lorentz action on the local field algebra

## i. Overview

The Lorentz group `SL(2,ℂ)` acts on the local field algebra `J(T)` of a field datum by
algebra endomorphisms: on the generators of a matter species by the action
`JetComponentSpace.repLorentzGroup` of that species, mixing the derivative label and the
target index, and on the connection generators by the gauge-only action
`LocalGaugeFieldAlgebra.repLorentzGroup`. The construction is that of the jet gauge action
in `Physlib.ClassicalFieldTheory.GaugeTheory.LocalFieldAlgebra.GaugeAction`: the lift of a
compatible assignment, with the representation laws from uniqueness.

## ii. Key results

- `GaugeFieldData.repLorentzAlgHom`, `GaugeFieldData.repLorentzGroup` : the action of a
  Lorentz transformation, as an algebra endomorphism and as a representation, with
  `repLorentzGroup_ιFermion`, `repLorentzGroup_ιBoson`, `repLorentzGroup_ιConnection` on the
  generators.
- `GaugeFieldData.repLorentzGroup_includeConnection` : on the connection factor the action
  is the complexified gauge-only action.
- `GaugeFieldData.repLorentzGroup_ιConnection_eq` : the law of the connection generators.

## iii. Table of contents

- A. The Lorentz assignment of a transformation
- B. The action of a transformation
- C. The action on the connection factor
- D. The representation

-/

@[expose] public section

open TensorProduct Matrix MatrixGroups

namespace GaugeFieldData

variable {G₀ : Type} [Group G₀] {𝔤 : Type} [LieRing 𝔤] [LieAlgebra ℝ 𝔤] [Module.Finite ℝ 𝔤]
  {GJ : Type} [Group GJ] {𝔤J : Type} [LieRing 𝔤J] [LieAlgebra ℝ 𝔤J]
  {jets : LocalGaugeData G₀ 𝔤 GJ 𝔤J} (T : GaugeFieldData jets)

/-!

## A. The Lorentz assignment of a transformation

-/

/-- The connection generators after a Lorentz transformation: the gauge-only action on the
  degree-one element, included into the local field algebra. -/
noncomputable def lorentzConnection (Λ : SL(2,ℂ)) :
    GaugeBoson.JetComponentSpace 𝔤 →ₗ[ℝ] T.LocalFieldAlgebra :=
  ((T.includeConnection).restrictScalars ℝ).toLinearMap ∘ₗ
    (Algebra.TensorProduct.includeRight (R := ℝ) (A := ℂ)
      (B := SymmetricAlgebra ℝ (GaugeBoson.JetComponentSpace 𝔤))).toLinearMap ∘ₗ
    (SymmetricAlgebra.map (GaugeBoson.JetComponentSpace.repLorentzGroup 𝔤 Λ)).toLinearMap ∘ₗ
    SymmetricAlgebra.ι ℝ (GaugeBoson.JetComponentSpace 𝔤)

/-- The assignment of the generators defining the action of a Lorentz transformation: each
  matter species acts on its own component functions, the connection generators through
  the gauge-only action. -/
noncomputable def lorentzAssignment (Λ : SL(2,ℂ)) : T.Assignment T.LocalFieldAlgebra where
  fermion i := T.ιFermion i ∘ₗ JetComponentSpace.repLorentzGroup (T.fermion i) Λ
  boson j := T.ιBoson j ∘ₗ JetComponentSpace.repLorentzGroup (T.boson j) Λ
  connection := T.lorentzConnection Λ
  fermion_mul_self i _ := ιFermion_mul_self i _
  fermion_mul_swap i j _ _ := ιFermion_mul_swap i j _ _
  boson_commute i j _ _ := ιBoson_commute i j _ _
  connection_commute _ _ := (Commute.all _ _).map T.includeConnection
  boson_commute_connection _ _ _ := (includeConnection_commute _ _).symm
  boson_commute_fermion j i _ _ := ιBoson_commute_ιFermion j i _ _
  connection_commute_fermion _ _ _ := includeConnection_commute _ _

/-!

## B. The action of a transformation

-/

/-- The action of a Lorentz transformation on the local field algebra, as an algebra
  endomorphism: the lift of its Lorentz assignment. -/
noncomputable def repLorentzAlgHom (Λ : SL(2,ℂ)) :
    T.LocalFieldAlgebra →ₐ[ℂ] T.LocalFieldAlgebra :=
  (T.lorentzAssignment Λ).lift

variable {T}

@[simp]
lemma repLorentzAlgHom_ιFermion (Λ : SL(2,ℂ)) (i : T.FermionSpecies)
    (x : JetComponentSpace (T.fermion i)) :
    T.repLorentzAlgHom Λ (T.ιFermion i x)
      = T.ιFermion i (JetComponentSpace.repLorentzGroup (T.fermion i) Λ x) :=
  (T.lorentzAssignment Λ).lift_ιFermion i x

@[simp]
lemma repLorentzAlgHom_ιBoson (Λ : SL(2,ℂ)) (j : T.BosonSpecies)
    (y : JetComponentSpace (T.boson j)) :
    T.repLorentzAlgHom Λ (T.ιBoson j y)
      = T.ιBoson j (JetComponentSpace.repLorentzGroup (T.boson j) Λ y) :=
  (T.lorentzAssignment Λ).lift_ιBoson j y

@[simp]
lemma repLorentzAlgHom_ιConnection (Λ : SL(2,ℂ)) (v : GaugeBoson.JetComponentSpace 𝔤) :
    T.repLorentzAlgHom Λ (T.ιConnection v)
      = T.includeConnection ((1 : ℂ) ⊗ₜ[ℝ]
          LocalGaugeFieldAlgebra.repLorentzGroup 𝔤 Λ (SymmetricAlgebra.ι ℝ _ v)) :=
  (T.lorentzAssignment Λ).lift_ιConnection v

/-!

## C. The action on the connection factor

-/

/-- The action of a Lorentz transformation restricts to the complexified gauge-only action
  on the connection factor, as an equation of algebra maps out of the complexified
  gauge-only algebra, compared on the real generators. -/
lemma repLorentzAlgHom_comp_includeConnection (Λ : SL(2,ℂ)) :
    (T.repLorentzAlgHom Λ).comp T.includeConnection
      = T.includeConnection.comp (LocalGaugeFieldAlgebra.complexRepLorentzGroupAlgHom 𝔤 Λ) := by
  refine Algebra.TensorProduct.ext (Subsingleton.elim _ _) ?_
  refine AlgHom.ext_of_adjoin_eq_top SymmetricAlgebra.adjoin_range_ι ?_
  rintro _ ⟨v, rfl⟩
  exact repLorentzAlgHom_ιConnection Λ v

/-- The action of a Lorentz transformation restricts to the complexified gauge-only action
  on the connection factor. -/
lemma repLorentzAlgHom_includeConnection (Λ : SL(2,ℂ)) (y : ℂ ⊗[ℝ] LocalGaugeFieldAlgebra 𝔤) :
    T.repLorentzAlgHom Λ (T.includeConnection y)
      = T.includeConnection (LocalGaugeFieldAlgebra.complexRepLorentzGroup 𝔤 Λ y) := by
  rw [LocalGaugeFieldAlgebra.complexRepLorentzGroup_apply]
  exact AlgHom.congr_fun (repLorentzAlgHom_comp_includeConnection Λ) y

/-- On the real gauge-only algebra, included, a Lorentz transformation acts through the
  gauge-only action. -/
lemma repLorentzAlgHom_includeConnection_one_tmul (Λ : SL(2,ℂ)) (x : LocalGaugeFieldAlgebra 𝔤) :
    T.repLorentzAlgHom Λ (T.includeConnection ((1 : ℂ) ⊗ₜ[ℝ] x))
      = T.includeConnection ((1 : ℂ) ⊗ₜ[ℝ] LocalGaugeFieldAlgebra.repLorentzGroup 𝔤 Λ x) :=
  repLorentzAlgHom_includeConnection Λ ((1 : ℂ) ⊗ₜ[ℝ] x)

/-!

## D. The representation

-/

/-- The identity transformation acts as the identity. -/
lemma repLorentzAlgHom_one : T.repLorentzAlgHom 1 = AlgHom.id ℂ T.LocalFieldAlgebra := by
  refine algHom_ext (fun i x => ?_) (fun j y => ?_) (fun v => ?_)
  · rw [repLorentzAlgHom_ιFermion, map_one, Module.End.one_apply, AlgHom.id_apply]
  · rw [repLorentzAlgHom_ιBoson, map_one, Module.End.one_apply, AlgHom.id_apply]
  · rw [repLorentzAlgHom_ιConnection, map_one, Module.End.one_apply, AlgHom.id_apply]
    rfl

/-- The action of a product of transformations is the composite of the actions. -/
lemma repLorentzAlgHom_mul (Λ₁ Λ₂ : SL(2,ℂ)) :
    T.repLorentzAlgHom (Λ₁ * Λ₂) = (T.repLorentzAlgHom Λ₁).comp (T.repLorentzAlgHom Λ₂) := by
  refine algHom_ext (fun i x => ?_) (fun j y => ?_) (fun v => ?_)
  · rw [repLorentzAlgHom_ιFermion, AlgHom.comp_apply, repLorentzAlgHom_ιFermion,
      repLorentzAlgHom_ιFermion, map_mul, Module.End.mul_apply]
  · rw [repLorentzAlgHom_ιBoson, AlgHom.comp_apply, repLorentzAlgHom_ιBoson,
      repLorentzAlgHom_ιBoson, map_mul, Module.End.mul_apply]
  · refine (repLorentzAlgHom_ιConnection (Λ₁ * Λ₂) v).trans ?_
    refine Eq.trans ?_
      (congrArg (T.repLorentzAlgHom Λ₁) (repLorentzAlgHom_ιConnection Λ₂ v)).symm
    refine Eq.trans ?_ (repLorentzAlgHom_includeConnection_one_tmul Λ₁ _).symm
    refine congrArg (fun z => T.includeConnection ((1 : ℂ) ⊗ₜ[ℝ] z)) ?_
    rw [map_mul (LocalGaugeFieldAlgebra.repLorentzGroup 𝔤), Module.End.mul_apply]

variable (T)

/-- The action of the Lorentz group on the local field algebra. -/
noncomputable def repLorentzGroup : Representation ℂ SL(2,ℂ) T.LocalFieldAlgebra where
  toFun Λ := (T.repLorentzAlgHom Λ).toLinearMap
  map_one' := LinearMap.ext fun x => AlgHom.congr_fun repLorentzAlgHom_one x
  map_mul' Λ₁ Λ₂ := LinearMap.ext fun x => AlgHom.congr_fun (repLorentzAlgHom_mul Λ₁ Λ₂) x

variable {T}

lemma repLorentzGroup_apply (Λ : SL(2,ℂ)) (x : T.LocalFieldAlgebra) :
    T.repLorentzGroup Λ x = T.repLorentzAlgHom Λ x := rfl

lemma repLorentzGroup_apply_mul (Λ : SL(2,ℂ)) (x y : T.LocalFieldAlgebra) :
    T.repLorentzGroup Λ (x * y) = T.repLorentzGroup Λ x * T.repLorentzGroup Λ y :=
  map_mul (T.repLorentzAlgHom Λ) x y

lemma repLorentzGroup_apply_one (Λ : SL(2,ℂ)) :
    T.repLorentzGroup Λ (1 : T.LocalFieldAlgebra) = 1 :=
  (T.repLorentzAlgHom Λ).map_one

@[simp]
lemma repLorentzGroup_ιFermion (Λ : SL(2,ℂ)) (i : T.FermionSpecies)
    (x : JetComponentSpace (T.fermion i)) :
    T.repLorentzGroup Λ (T.ιFermion i x)
      = T.ιFermion i (JetComponentSpace.repLorentzGroup (T.fermion i) Λ x) :=
  repLorentzAlgHom_ιFermion Λ i x

@[simp]
lemma repLorentzGroup_ιBoson (Λ : SL(2,ℂ)) (j : T.BosonSpecies)
    (y : JetComponentSpace (T.boson j)) :
    T.repLorentzGroup Λ (T.ιBoson j y)
      = T.ιBoson j (JetComponentSpace.repLorentzGroup (T.boson j) Λ y) :=
  repLorentzAlgHom_ιBoson Λ j y

@[simp]
lemma repLorentzGroup_ιConnection (Λ : SL(2,ℂ)) (v : GaugeBoson.JetComponentSpace 𝔤) :
    T.repLorentzGroup Λ (T.ιConnection v)
      = T.includeConnection ((1 : ℂ) ⊗ₜ[ℝ]
          LocalGaugeFieldAlgebra.repLorentzGroup 𝔤 Λ (SymmetricAlgebra.ι ℝ _ v)) :=
  repLorentzAlgHom_ιConnection Λ v

/-- The Lorentz action restricts to the complexified gauge-only action on the connection
  factor. -/
lemma repLorentzGroup_includeConnection (Λ : SL(2,ℂ)) (y : ℂ ⊗[ℝ] LocalGaugeFieldAlgebra 𝔤) :
    T.repLorentzGroup Λ (T.includeConnection y)
      = T.includeConnection (LocalGaugeFieldAlgebra.complexRepLorentzGroup 𝔤 Λ y) :=
  repLorentzAlgHom_includeConnection Λ y

/-- The Lorentz law of the connection generators: a transformation carries a connection
  generator to the generator of the transformed component, with no shift. This is the
  generator-level form of `GaugeFieldData.repLorentzGroup_ιConnection`, with no reference
  to the connection factor. -/
lemma repLorentzGroup_ιConnection_eq (Λ : SL(2,ℂ)) (v : GaugeBoson.JetComponentSpace 𝔤) :
    T.repLorentzGroup Λ (T.ιConnection v)
      = T.ιConnection (GaugeBoson.JetComponentSpace.repLorentzGroup 𝔤 Λ v) := by
  rw [repLorentzGroup_ιConnection, LocalGaugeFieldAlgebra.repLorentzGroup_ι]
  rfl

end GaugeFieldData
