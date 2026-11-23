/-
Copyright (c) 2026 Nathaneal Sajan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.LocalFieldAlgebra.Basic
/-!
# The jet gauge action on the local field algebra

The action of the jet gauge group on the local field algebra by algebra endomorphisms.

## i. Overview

The jet gauge group `G.gaugeJetGroup` acts on the local field algebra `J(T)` of a field datum
by algebra endomorphisms. It acts on the generators of a matter species by the action
`FieldDerivSpace.repJet` of that species, and on the connection generators by the affine
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

## iv. References

* None.

-/

@[expose] public section

open TensorProduct

namespace GaugeFieldData

variable {κ : Type} [Fintype κ] [DecidableEq κ] {G : GlobalGaugeGroup κ} (T : GaugeFieldData G)

/-!

## A. The gauge assignment of a jet

-/

/-- The connection generators after the action of a jet, the gauge-only action on the
  degree-one element, included into the local field algebra. -/
noncomputable def gaugeConnection (U : G.gaugeJetGroup) :
    GaugeBoson.FieldDerivSpace G →ₗ[ℝ] T.LocalFieldAlgebra :=
  ((T.includeConnection).restrictScalars ℝ).toLinearMap ∘ₗ
    (Algebra.TensorProduct.includeRight (R := ℝ) (A := ℂ)
      (B := SymmetricAlgebra ℝ (GaugeBoson.FieldDerivSpace G))).toLinearMap ∘ₗ
    (LocalGaugeFieldAlgebra.repJetAlgHom G U).toLinearMap ∘ₗ
    SymmetricAlgebra.ι ℝ (GaugeBoson.FieldDerivSpace G)

/-- The assignment of the generators defining the action of a jet. Each matter species
  acts on its own component functions, the connection generators through the gauge-only
  action. The relations hold because the images are generators of the same kind, or lie in
  the central connection factor. -/
noncomputable def gaugeAssignment (U : G.gaugeJetGroup) : T.Assignment T.LocalFieldAlgebra where
  fermion i := T.ιFermion i ∘ₗ FieldDerivSpace.repJet (T.fermion i) U
  boson j := T.ιBoson j ∘ₗ FieldDerivSpace.repJet (T.boson j) U
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

/-- The action of a jet on the local field algebra, as an algebra endomorphism, the lift
  of its gauge assignment. -/
noncomputable def repJetAlgHom (U : G.gaugeJetGroup) : T.LocalFieldAlgebra →ₐ[ℂ]
  T.LocalFieldAlgebra :=
  (T.gaugeAssignment U).lift

variable {T}

@[simp]
lemma repJetAlgHom_ιFermion (U : G.gaugeJetGroup) (i : T.FermionSpecies)
    (x : FieldDerivSpace (T.fermion i)) :
    T.repJetAlgHom U (T.ιFermion i x)
      = T.ιFermion i (FieldDerivSpace.repJet (T.fermion i) U x) :=
  (T.gaugeAssignment U).lift_ιFermion i x

@[simp]
lemma repJetAlgHom_ιBoson (U : G.gaugeJetGroup) (j : T.BosonSpecies)
    (y : FieldDerivSpace (T.boson j)) :
    T.repJetAlgHom U (T.ιBoson j y) = T.ιBoson j (FieldDerivSpace.repJet (T.boson j) U y) :=
  (T.gaugeAssignment U).lift_ιBoson j y

@[simp]
lemma repJetAlgHom_ιConnection (U : G.gaugeJetGroup) (v : GaugeBoson.FieldDerivSpace G) :
    T.repJetAlgHom U (T.ιConnection v)
      = T.includeConnection ((1 : ℂ) ⊗ₜ[ℝ]
          LocalGaugeFieldAlgebra.repJet G U (SymmetricAlgebra.ι ℝ _ v)) :=
  (T.gaugeAssignment U).lift_ιConnection v

/-!

## C. The action on the connection factor

-/

/-- The action of a jet restricts to the complexified gauge-only action on the connection
  factor, as an equation of algebra maps out of the complexified gauge-only algebra. It is
  enough to compare them on the real generators, where it is the computation rule of the
  lift. -/
lemma repJetAlgHom_comp_includeConnection (U : G.gaugeJetGroup) :
    (T.repJetAlgHom U).comp T.includeConnection
      = T.includeConnection.comp (LocalGaugeFieldAlgebra.complexRepJetAlgHom G U) := by
  refine Algebra.TensorProduct.ext (Subsingleton.elim _ _) ?_
  refine AlgHom.ext_of_adjoin_eq_top SymmetricAlgebra.adjoin_range_ι ?_
  rintro _ ⟨v, rfl⟩
  exact repJetAlgHom_ιConnection U v

/-- The action of a jet restricts to the complexified gauge-only action on the connection
  factor. -/
lemma repJetAlgHom_includeConnection (U : G.gaugeJetGroup) (y : ℂ ⊗[ℝ] LocalGaugeFieldAlgebra G) :
    T.repJetAlgHom U (T.includeConnection y)
      = T.includeConnection (LocalGaugeFieldAlgebra.complexRepJet G U y) := by
  rw [LocalGaugeFieldAlgebra.complexRepJet_apply]
  exact AlgHom.congr_fun (repJetAlgHom_comp_includeConnection U) y

/-- On the real gauge-only algebra, included, a jet acts through the gauge-only action. -/
lemma repJetAlgHom_includeConnection_one_tmul (U : G.gaugeJetGroup) (x : LocalGaugeFieldAlgebra G) :
    T.repJetAlgHom U (T.includeConnection ((1 : ℂ) ⊗ₜ[ℝ] x))
      = T.includeConnection ((1 : ℂ) ⊗ₜ[ℝ] LocalGaugeFieldAlgebra.repJet G U x) :=
  repJetAlgHom_includeConnection U ((1 : ℂ) ⊗ₜ[ℝ] x)

/-!

## D. The representation

-/

/-- The identity jet acts as the identity. -/
lemma repJetAlgHom_one : T.repJetAlgHom 1 = AlgHom.id ℂ T.LocalFieldAlgebra := by
  refine algHom_ext (fun i x => ?_) (fun j y => ?_) (fun v => ?_)
  · rw [repJetAlgHom_ιFermion, map_one, one_apply_eq_self, AlgHom.id_apply]
  · rw [repJetAlgHom_ιBoson, map_one, one_apply_eq_self, AlgHom.id_apply]
  · rw [repJetAlgHom_ιConnection, map_one, one_apply_eq_self, AlgHom.id_apply]
    rfl

/-- The action of a product of jets is the composite of the actions. -/
lemma repJetAlgHom_mul (U V : G.gaugeJetGroup) :
    T.repJetAlgHom (U * V) = (T.repJetAlgHom U).comp (T.repJetAlgHom V) := by
  refine algHom_ext (fun i x => ?_) (fun j y => ?_) (fun v => ?_)
  · rw [repJetAlgHom_ιFermion, AlgHom.comp_apply, repJetAlgHom_ιFermion, repJetAlgHom_ιFermion,
      map_mul, mul_apply_eq_comp]
  · rw [repJetAlgHom_ιBoson, AlgHom.comp_apply, repJetAlgHom_ιBoson, repJetAlgHom_ιBoson,
      map_mul, mul_apply_eq_comp]
  · refine (repJetAlgHom_ιConnection (U * V) v).trans ?_
    refine Eq.trans ?_ (congrArg (T.repJetAlgHom U) (repJetAlgHom_ιConnection V v)).symm
    refine Eq.trans ?_ (repJetAlgHom_includeConnection_one_tmul U _).symm
    refine congrArg (fun z => T.includeConnection ((1 : ℂ) ⊗ₜ[ℝ] z)) ?_
    rw [map_mul (LocalGaugeFieldAlgebra.repJet G), mul_apply_eq_comp]

variable (T)

/-- The action of the jet gauge group on the local field algebra. -/
noncomputable def repJet : Representation ℂ G.gaugeJetGroup T.LocalFieldAlgebra where
  toFun U := (T.repJetAlgHom U).toLinearMap
  map_one' := LinearMap.ext fun x => AlgHom.congr_fun repJetAlgHom_one x
  map_mul' U V := LinearMap.ext fun x => AlgHom.congr_fun (repJetAlgHom_mul U V) x

variable {T}

lemma repJet_apply (U : G.gaugeJetGroup) (x : T.LocalFieldAlgebra) :
    T.repJet U x = T.repJetAlgHom U x := rfl

lemma repJet_apply_mul (U : G.gaugeJetGroup) (x y : T.LocalFieldAlgebra) :
    T.repJet U (x * y) = T.repJet U x * T.repJet U y :=
  map_mul (T.repJetAlgHom U) x y

lemma repJet_apply_one (U : G.gaugeJetGroup) : T.repJet U (1 : T.LocalFieldAlgebra) = 1 :=
  (T.repJetAlgHom U).map_one

@[simp]
lemma repJet_ιFermion (U : G.gaugeJetGroup) (i : T.FermionSpecies)
    (x : FieldDerivSpace (T.fermion i)) :
    T.repJet U (T.ιFermion i x) = T.ιFermion i (FieldDerivSpace.repJet (T.fermion i) U x) :=
  repJetAlgHom_ιFermion U i x

@[simp]
lemma repJet_ιBoson (U : G.gaugeJetGroup) (j : T.BosonSpecies) (y : FieldDerivSpace (T.boson j)) :
    T.repJet U (T.ιBoson j y) = T.ιBoson j (FieldDerivSpace.repJet (T.boson j) U y) :=
  repJetAlgHom_ιBoson U j y

@[simp]
lemma repJet_ιConnection (U : G.gaugeJetGroup) (v : GaugeBoson.FieldDerivSpace G) :
    T.repJet U (T.ιConnection v)
      = T.includeConnection ((1 : ℂ) ⊗ₜ[ℝ]
          LocalGaugeFieldAlgebra.repJet G U (SymmetricAlgebra.ι ℝ _ v)) :=
  repJetAlgHom_ιConnection U v

/-- The jet gauge action restricts to the complexified gauge-only action on the connection
  factor. -/
lemma repJet_includeConnection (U : G.gaugeJetGroup) (y : ℂ ⊗[ℝ] LocalGaugeFieldAlgebra G) :
    T.repJet U (T.includeConnection y)
      = T.includeConnection (LocalGaugeFieldAlgebra.complexRepJet G U y) :=
  repJetAlgHom_includeConnection U y

/-- The affine gauge law of the connection generators. A jet carries a connection
  generator to the transported generator of its inverse plus the Maurer–Cartan shift, the
  gauge field being a connection and not a tensor. This is the generator-level form of
  `GaugeFieldData.repJet_ιConnection`, with no reference to the connection factor. -/
lemma repJet_ιConnection_affine (U : G.gaugeJetGroup) (v : GaugeBoson.FieldDerivSpace G) :
    T.repJet U (T.ιConnection v)
      = T.ιConnection (LocalGaugeFieldAlgebra.transport G U⁻¹ v)
        + (LocalGaugeFieldAlgebra.maurerCartanShift G U⁻¹ v : ℂ) •
          (1 : T.LocalFieldAlgebra) := by
  rw [repJet_ιConnection, LocalGaugeFieldAlgebra.repJet_ι, TensorProduct.tmul_add, map_add,
    show ((1 : ℂ) ⊗ₜ[ℝ] algebraMap ℝ (LocalGaugeFieldAlgebra G)
        (LocalGaugeFieldAlgebra.maurerCartanShift G U⁻¹ v))
      = algebraMap ℝ (ℂ ⊗[ℝ] LocalGaugeFieldAlgebra G)
          (LocalGaugeFieldAlgebra.maurerCartanShift G U⁻¹ v) from
      (Algebra.TensorProduct.includeRight_apply _).symm.trans
        (AlgHom.commutes Algebra.TensorProduct.includeRight _),
    IsScalarTower.algebraMap_apply ℝ ℂ (ℂ ⊗[ℝ] LocalGaugeFieldAlgebra G),
      AlgHom.commutes,
    Algebra.algebraMap_eq_smul_one]
  rfl

end GaugeFieldData
