/-
Copyright (c) 2026 Nathaneal Sajan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaneal Sajan
-/
module

public import Physlib.ClassicalFieldTheory.GaugeTheory.LocalFieldAlgebra.Basic
public import Physlib.ClassicalFieldTheory.GaugeTheory.GaugeBoson.LocalGaugeFieldAlgebra.GaugeAction
/-!
# The jet gauge action on the local field algebra

## i. Overview

The jet gauge group `GJ` acts on the local field algebra `J(T)` of a field datum by algebra
endomorphisms: on the generators of a matter species by the action
`JetComponentSpace.repJet` of that species, and on the connection generators by the affine
action `LocalGaugeFieldAlgebra.repJet` of the gauge-only algebra, with its Maurer–Cartan
shift. The three generator actions form a compatible assignment, whose lift through the
universal property of `J(T)` is the action of one jet; the representation laws follow from
uniqueness, without unfolding the tensor-product carrier.

## ii. Key results

- `GaugeFieldData.repJetAlgHom`, `GaugeFieldData.repJet` : the action of a jet, as an
  algebra endomorphism and as a representation, with `repJet_ιFermion`, `repJet_ιBoson`,
  `repJet_ιConnection` on the generators.
- `GaugeFieldData.repJet_includeConnection` : on the connection factor the action is the
  complexified gauge-only action.
- `GaugeFieldData.repJet_ιConnection_affine` : the affine law of the connection generators.

## iii. Table of contents

- A. The gauge assignment of a jet
- B. The action of a jet
- C. The action on the connection factor
- D. The representation

-/

@[expose] public section

open TensorProduct

namespace GaugeFieldData

variable {G₀ : Type} [Group G₀] {𝔤 : Type} [LieRing 𝔤] [LieAlgebra ℝ 𝔤] [Module.Finite ℝ 𝔤]
  {GJ : Type} [Group GJ] {𝔤J : Type} [LieRing 𝔤J] [LieAlgebra ℝ 𝔤J]
  {jets : LocalGaugeData G₀ 𝔤 GJ 𝔤J} (T : GaugeFieldData jets)

/-!

## A. The gauge assignment of a jet

-/

/-- The connection generators after the action of a jet: the gauge-only action on the
  degree-one element, included into the local field algebra. -/
noncomputable def gaugeConnection (U : GJ) :
    GaugeBoson.JetComponentSpace 𝔤 →ₗ[ℝ] T.LocalFieldAlgebra :=
  ((T.includeConnection).restrictScalars ℝ).toLinearMap ∘ₗ
    (Algebra.TensorProduct.includeRight (R := ℝ) (A := ℂ)
      (B := SymmetricAlgebra ℝ (GaugeBoson.JetComponentSpace 𝔤))).toLinearMap ∘ₗ
    (LocalGaugeFieldAlgebra.repJetAlgHom jets U).toLinearMap ∘ₗ
    SymmetricAlgebra.ι ℝ (GaugeBoson.JetComponentSpace 𝔤)

/-- The assignment of the generators defining the action of a jet: each matter species
  acts on its own component functions, the connection generators through the gauge-only
  action. The relations hold because the images are generators of the same kind, or lie in
  the central connection factor. -/
noncomputable def gaugeAssignment (U : GJ) : T.Assignment T.LocalFieldAlgebra where
  fermion i := T.ιFermion i ∘ₗ JetComponentSpace.repJet (T.fermion i) U
  boson j := T.ιBoson j ∘ₗ JetComponentSpace.repJet (T.boson j) U
  connection := T.gaugeConnection U
  fermion_mul_self i _ := ιFermion_mul_self i _
  fermion_mul_swap i j _ _ := ιFermion_mul_swap i j _ _
  boson_commute i j _ _ := ιBoson_commute i j _ _
  connection_commute _ _ := (Commute.all _ _).map T.includeConnection
  boson_commute_connection _ _ _ := (includeConnection_commute _ _).symm
  boson_commute_fermion j i _ _ := ιBoson_commute_ιFermion j i _ _
  connection_commute_fermion _ _ _ := includeConnection_commute _ _

/-!

## B. The action of a jet

-/

/-- The action of a jet on the local field algebra, as an algebra endomorphism: the lift
  of its gauge assignment. -/
noncomputable def repJetAlgHom (U : GJ) : T.LocalFieldAlgebra →ₐ[ℂ] T.LocalFieldAlgebra :=
  (T.gaugeAssignment U).lift

variable {T}

@[simp]
lemma repJetAlgHom_ιFermion (U : GJ) (i : T.FermionSpecies)
    (x : JetComponentSpace (T.fermion i)) :
    T.repJetAlgHom U (T.ιFermion i x)
      = T.ιFermion i (JetComponentSpace.repJet (T.fermion i) U x) :=
  (T.gaugeAssignment U).lift_ιFermion i x

@[simp]
lemma repJetAlgHom_ιBoson (U : GJ) (j : T.BosonSpecies) (y : JetComponentSpace (T.boson j)) :
    T.repJetAlgHom U (T.ιBoson j y) = T.ιBoson j (JetComponentSpace.repJet (T.boson j) U y) :=
  (T.gaugeAssignment U).lift_ιBoson j y

@[simp]
lemma repJetAlgHom_ιConnection (U : GJ) (v : GaugeBoson.JetComponentSpace 𝔤) :
    T.repJetAlgHom U (T.ιConnection v)
      = T.includeConnection ((1 : ℂ) ⊗ₜ[ℝ]
          LocalGaugeFieldAlgebra.repJet jets U (SymmetricAlgebra.ι ℝ _ v)) :=
  (T.gaugeAssignment U).lift_ιConnection v

/-!

## C. The action on the connection factor

-/

/-- The action of a jet restricts to the complexified gauge-only action on the connection
  factor, as an equation of algebra maps out of the complexified gauge-only algebra: it is
  enough to compare them on the real generators, where it is the computation rule of the
  lift. -/
lemma repJetAlgHom_comp_includeConnection (U : GJ) :
    (T.repJetAlgHom U).comp T.includeConnection
      = T.includeConnection.comp (LocalGaugeFieldAlgebra.complexRepJetAlgHom jets U) := by
  refine Algebra.TensorProduct.ext (Subsingleton.elim _ _) ?_
  refine AlgHom.ext_of_adjoin_eq_top SymmetricAlgebra.adjoin_range_ι ?_
  rintro _ ⟨v, rfl⟩
  exact repJetAlgHom_ιConnection U v

/-- The action of a jet restricts to the complexified gauge-only action on the connection
  factor. -/
lemma repJetAlgHom_includeConnection (U : GJ) (y : ℂ ⊗[ℝ] LocalGaugeFieldAlgebra 𝔤) :
    T.repJetAlgHom U (T.includeConnection y)
      = T.includeConnection (LocalGaugeFieldAlgebra.complexRepJet jets U y) := by
  rw [LocalGaugeFieldAlgebra.complexRepJet_apply]
  exact AlgHom.congr_fun (repJetAlgHom_comp_includeConnection U) y

/-- On the real gauge-only algebra, included, a jet acts through the gauge-only action. -/
lemma repJetAlgHom_includeConnection_one_tmul (U : GJ) (x : LocalGaugeFieldAlgebra 𝔤) :
    T.repJetAlgHom U (T.includeConnection ((1 : ℂ) ⊗ₜ[ℝ] x))
      = T.includeConnection ((1 : ℂ) ⊗ₜ[ℝ] LocalGaugeFieldAlgebra.repJet jets U x) :=
  repJetAlgHom_includeConnection U ((1 : ℂ) ⊗ₜ[ℝ] x)

/-!

## D. The representation

-/

/-- The identity jet acts as the identity. -/
lemma repJetAlgHom_one : T.repJetAlgHom 1 = AlgHom.id ℂ T.LocalFieldAlgebra := by
  refine algHom_ext (fun i x => ?_) (fun j y => ?_) (fun v => ?_)
  · rw [repJetAlgHom_ιFermion, map_one, Module.End.one_apply, AlgHom.id_apply]
  · rw [repJetAlgHom_ιBoson, map_one, Module.End.one_apply, AlgHom.id_apply]
  · rw [repJetAlgHom_ιConnection, map_one, Module.End.one_apply, AlgHom.id_apply]
    rfl

/-- The action of a product of jets is the composite of the actions. -/
lemma repJetAlgHom_mul (U V : GJ) :
    T.repJetAlgHom (U * V) = (T.repJetAlgHom U).comp (T.repJetAlgHom V) := by
  refine algHom_ext (fun i x => ?_) (fun j y => ?_) (fun v => ?_)
  · rw [repJetAlgHom_ιFermion, AlgHom.comp_apply, repJetAlgHom_ιFermion, repJetAlgHom_ιFermion,
      map_mul, Module.End.mul_apply]
  · rw [repJetAlgHom_ιBoson, AlgHom.comp_apply, repJetAlgHom_ιBoson, repJetAlgHom_ιBoson,
      map_mul, Module.End.mul_apply]
  · refine (repJetAlgHom_ιConnection (U * V) v).trans ?_
    refine Eq.trans ?_ (congrArg (T.repJetAlgHom U) (repJetAlgHom_ιConnection V v)).symm
    refine Eq.trans ?_ (repJetAlgHom_includeConnection_one_tmul U _).symm
    refine congrArg (fun z => T.includeConnection ((1 : ℂ) ⊗ₜ[ℝ] z)) ?_
    rw [map_mul (LocalGaugeFieldAlgebra.repJet jets), Module.End.mul_apply]

variable (T)

/-- The action of the jet gauge group on the local field algebra. -/
noncomputable def repJet : Representation ℂ GJ T.LocalFieldAlgebra where
  toFun U := (T.repJetAlgHom U).toLinearMap
  map_one' := LinearMap.ext fun x => AlgHom.congr_fun repJetAlgHom_one x
  map_mul' U V := LinearMap.ext fun x => AlgHom.congr_fun (repJetAlgHom_mul U V) x

variable {T}

lemma repJet_apply (U : GJ) (x : T.LocalFieldAlgebra) :
    T.repJet U x = T.repJetAlgHom U x := rfl

lemma repJet_apply_mul (U : GJ) (x y : T.LocalFieldAlgebra) :
    T.repJet U (x * y) = T.repJet U x * T.repJet U y :=
  map_mul (T.repJetAlgHom U) x y

lemma repJet_apply_one (U : GJ) : T.repJet U (1 : T.LocalFieldAlgebra) = 1 :=
  (T.repJetAlgHom U).map_one

@[simp]
lemma repJet_ιFermion (U : GJ) (i : T.FermionSpecies) (x : JetComponentSpace (T.fermion i)) :
    T.repJet U (T.ιFermion i x) = T.ιFermion i (JetComponentSpace.repJet (T.fermion i) U x) :=
  repJetAlgHom_ιFermion U i x

@[simp]
lemma repJet_ιBoson (U : GJ) (j : T.BosonSpecies) (y : JetComponentSpace (T.boson j)) :
    T.repJet U (T.ιBoson j y) = T.ιBoson j (JetComponentSpace.repJet (T.boson j) U y) :=
  repJetAlgHom_ιBoson U j y

@[simp]
lemma repJet_ιConnection (U : GJ) (v : GaugeBoson.JetComponentSpace 𝔤) :
    T.repJet U (T.ιConnection v)
      = T.includeConnection ((1 : ℂ) ⊗ₜ[ℝ]
          LocalGaugeFieldAlgebra.repJet jets U (SymmetricAlgebra.ι ℝ _ v)) :=
  repJetAlgHom_ιConnection U v

/-- The jet gauge action restricts to the complexified gauge-only action on the connection
  factor. -/
lemma repJet_includeConnection (U : GJ) (y : ℂ ⊗[ℝ] LocalGaugeFieldAlgebra 𝔤) :
    T.repJet U (T.includeConnection y)
      = T.includeConnection (LocalGaugeFieldAlgebra.complexRepJet jets U y) :=
  repJetAlgHom_includeConnection U y

/-- The affine gauge law of the connection generators: a jet carries a connection
  generator to the transported generator of its inverse plus the Maurer–Cartan shift, the
  gauge field being a connection and not a tensor. This is the generator-level form of
  `GaugeFieldData.repJet_ιConnection`, with no reference to the connection factor. -/
lemma repJet_ιConnection_affine (U : GJ) (v : GaugeBoson.JetComponentSpace 𝔤) :
    T.repJet U (T.ιConnection v)
      = T.ιConnection (LocalGaugeFieldAlgebra.transport jets U⁻¹ v)
        + (LocalGaugeFieldAlgebra.mcShift jets U⁻¹ v : ℂ) • (1 : T.LocalFieldAlgebra) := by
  rw [repJet_ιConnection, LocalGaugeFieldAlgebra.repJet_ι, TensorProduct.tmul_add, map_add,
    show ((1 : ℂ) ⊗ₜ[ℝ] algebraMap ℝ (LocalGaugeFieldAlgebra 𝔤)
        (LocalGaugeFieldAlgebra.mcShift jets U⁻¹ v))
      = algebraMap ℝ (ℂ ⊗[ℝ] LocalGaugeFieldAlgebra 𝔤)
          (LocalGaugeFieldAlgebra.mcShift jets U⁻¹ v) from
      (Algebra.TensorProduct.includeRight_apply _).symm.trans
        (AlgHom.commutes Algebra.TensorProduct.includeRight _),
    IsScalarTower.algebraMap_apply ℝ ℂ (ℂ ⊗[ℝ] LocalGaugeFieldAlgebra 𝔤), AlgHom.commutes,
    Algebra.algebraMap_eq_smul_one]
  rfl

end GaugeFieldData
