/-
Copyright (c) 2026 Nathaneal Sajan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaneal Sajan
-/
module

public import Physlib.Particles.StandardModel.JetAlgebra.SectorEquiv.Basic
public import Physlib.Particles.StandardModel.Fermions.JetAlgebra.Species
/-!
# The generator identifications respect the transformation data

## i. Overview

`Physlib.Particles.StandardModel.JetAlgebra.SectorEquiv.Basic` identifies the two matter
generator spaces of `StandardModel.fieldData` with the two the Standard Model sector
algebras are built on. This file proves that those identifications respect the
transformation data: the Lorentz action, the jet gauge action and the mass weights.

The generic half of each statement is already proved once and for all in
`Physlib.ClassicalFieldTheory.GaugeTheory.GaugeFieldData.FermionGenerators`:
`GaugeFieldData.fermionGeneratorsEquiv` intertwines the species-diagonal Lorentz and jet
gauge actions on the direct sum with the actions on the component functions of a single
field valued in `T.FermionModule`, and likewise for the mass-weight scaling under a common
weight. What is added here is the Standard Model half: the relabelling `fermionSpaceEquiv`
of the target space is itself equivariant for both actions, which is the two families of
five species lemmas of
`Physlib.Particles.StandardModel.Fermions.JetAlgebra.Species` read at the fifteen species
of the datum. Naturality of `JetComponentSpace.comap` in the value space then carries the
generic statements across the relabelling; for the mass-weight scaling no equivariance is
needed at all, the scaling being blind to the value space.

Gauge equivariance is the one statement of the three that is not formal. The gauge action
on a component function is the all-orders Leibniz convolution of the Taylor coefficients of
the gauge jet, so it sees the derivative label as well as the target index, and its
conjugate half carries `star` of the gauge matrix rather than the matrix. Neither half
follows from the other, and neither follows from linearity: both are proved, for every
derivative label, from `JetComponentSpace.comap_comp_repJet`. No common mass weight enters
any of it — the fifteen fermionic species do share weight three, but the gauge statement
does not use that, and is stated over `GaugeFieldData.repJetFermionModule`, which is
defined whatever the weights are.

Section C lifts the four resulting generator statements to the sector algebras, which are
the two matter factors of the carrier. The ordinary derivative is treated in section D of
`Physlib.Particles.StandardModel.JetAlgebra.SectorEquiv.Basic`. The connection sector needs
no identification at all: the Standard Model gauge bosons are the generic ones at
`GaugeAlgebra`.

## ii. Key results

- `StandardModel.fermionSpaceEquiv_comp_repLorentzGroup`,
  `StandardModel.lTensor_fermionSpaceEquiv_repJetGaugeGroupI` : the relabelling of the
  fermionic target space is equivariant for the Lorentz and the jet gauge action.
- `StandardModel.fermionGeneratorsEquiv_repLorentzFermion`,
  `StandardModel.bosonGeneratorsEquiv_repLorentzBoson` : the generator identifications
  intertwine the Lorentz actions.
- `StandardModel.fermionGeneratorsEquiv_repJetFermion`,
  `StandardModel.bosonGeneratorsEquiv_repJetBoson` : and the jet gauge actions.
- `StandardModel.fermionGeneratorsEquiv_massWeightScaleFermion`,
  `StandardModel.bosonGeneratorsEquiv_massWeightScaleBoson` : and the mass-weight
  scalings.
- `StandardModel.fermionAlgebraEquiv_repJetGaugeGroupI`,
  `StandardModel.higgsAlgebraEquiv_repJetGaugeGroupI`,
  `StandardModel.fermionAlgebraEquiv_repLorentzGroup`,
  `StandardModel.higgsAlgebraEquiv_repLorentzGroup` : the sector algebra equivalences
  intertwine both actions.

## iii. Table of contents

- A. The relabellings intertwine the Standard Model structure
  - A.1. The Lorentz action
  - A.2. The jet gauge action
- B. The generator identifications intertwine the transformation data
  - B.1. The Lorentz action
  - B.2. The jet gauge action
  - B.3. The mass weights
- C. The sector algebra equivalences intertwine the two actions

-/

@[expose] public section

open TensorProduct Matrix MatrixGroups

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000
set_option synthInstance.maxSize 2048
set_option maxRecDepth 8000

namespace StandardModel

/-!

## A. The relabellings intertwine the Standard Model structure

Both actions on the total fermionic target space are species-diagonal, which is already
recorded species by species in
`Physlib.Particles.StandardModel.Fermions.JetAlgebra.Species`. Reading those two families
of five lemmas at the fifteen species of the datum is the only Standard Model input the
comparison of the transformation data needs.

### A.1. The Lorentz action

-/

/-- The projection onto a species intertwines the total Lorentz action on the fermionic
  target space with that species' own. -/
lemma fermionProj_comp_repLorentzGroup (t : fieldData.FermionSpecies) (Λ : SL(2,ℂ)) :
    (fermionProj t).comp (FermionSpace.repLorentzGroup Λ)
      = ((fieldData.fermion t).repLorentz Λ).comp (fermionProj t) := by
  cases t with
  | leptonDoublet i => exact FermionSpace.leptonDoubletProj_comp_repLorentzGroup i Λ
  | leptonSinglet i => exact FermionSpace.leptonSingletProj_comp_repLorentzGroup i Λ
  | quarkDoublet i => exact FermionSpace.quarkDoubletProj_comp_repLorentzGroup i Λ
  | upSinglet i => exact FermionSpace.upSingletProj_comp_repLorentzGroup i Λ
  | downSinglet i => exact FermionSpace.downSingletProj_comp_repLorentzGroup i Λ

/-- The relabelling of the fermionic target space is Lorentz-equivariant. Both actions
  are species-diagonal, so this is the previous lemma read one species at a time. -/
lemma fermionSpaceEquiv_comp_repLorentzGroup (Λ : SL(2,ℂ)) :
    fermionSpaceEquiv.toLinearMap.comp (FermionSpace.repLorentzGroup Λ)
      = (fieldData.repLorentzFermionModule Λ).comp fermionSpaceEquiv.toLinearMap :=
  LinearMap.ext fun v => funext fun t =>
    LinearMap.congr_fun (fermionProj_comp_repLorentzGroup t Λ) v

/-- The relabelling of the Higgs is Lorentz-equivariant. The Higgs is a Lorentz scalar,
  so both sides are the identity; the content is that the one bosonic species of the datum
  carries exactly the trivial Higgs representation. -/
lemma higgsModuleEquiv_comp_repLorentzGroup (Λ : SL(2,ℂ)) :
    higgsModuleEquiv.toLinearMap.comp (Representation.trivial ℂ SL(2,ℂ) HiggsVec Λ)
      = (fieldData.repLorentzBosonModule Λ).comp higgsModuleEquiv.toLinearMap :=
  LinearMap.ext fun _ => funext fun _ => rfl

/-!

### A.2. The jet gauge action

The jet gauge action on the total fermionic target space is species-diagonal through
`FermionSpace.jetActionMap`, so each projection intertwines it with that species' own.
The relabelling is the assembly of the fifteen projections, and a jet of the fermionic
module is determined by its species components, so the relabelling too is equivariant.

-/

/-- The projection onto a species intertwines the total jet gauge action on the jets of
  the fermionic target space with that species' own. -/
lemma lTensor_fermionProj_repJetGaugeGroupI (t : fieldData.FermionSpecies)
    (U : JetGaugeGroupI) :
    (LinearMap.lTensor JetRing (fermionProj t)).comp (fermionMatterField.repJet U)
      = ((fieldData.fermion t).repJet U).comp
        (LinearMap.lTensor JetRing (fermionProj t)) := by
  cases t with
  | leptonDoublet i => exact FermionSpace.lTensor_leptonDoubletProj_repJetGaugeGroupI i U
  | leptonSinglet i => exact FermionSpace.lTensor_leptonSingletProj_repJetGaugeGroupI i U
  | quarkDoublet i => exact FermionSpace.lTensor_quarkDoubletProj_repJetGaugeGroupI i U
  | upSinglet i => exact FermionSpace.lTensor_upSingletProj_repJetGaugeGroupI i U
  | downSinglet i => exact FermionSpace.lTensor_downSingletProj_repJetGaugeGroupI i U

/-- The relabelling of the fermionic target space is equivariant for the jet gauge
  action. Both actions are species-diagonal, so this is the previous lemma read one
  species at a time, the two being compared through the splitting of the jets of a
  product. -/
lemma lTensor_fermionSpaceEquiv_repJetGaugeGroupI (U : JetGaugeGroupI) :
    (LinearMap.lTensor JetRing fermionSpaceEquiv.toLinearMap).comp
        (fermionMatterField.repJet U)
      = ((fieldData.fermionMatterField 3 fieldData_fermion_massWeight).repJet U).comp
        (LinearMap.lTensor JetRing fermionSpaceEquiv.toLinearMap) := by
  refine jetPi_hom_ext (fun i => (fieldData.fermion i).V) fun i => ?_
  have h1 : (LinearMap.lTensor JetRing (fieldData.projFermionField 3 fieldData_fermion_massWeight i)).comp
      (LinearMap.lTensor JetRing fermionSpaceEquiv.toLinearMap)
      = LinearMap.lTensor JetRing (fermionProj i) := by
    rw [← LinearMap.lTensor_comp]
    rfl
  refine LinearMap.ext fun x => ?_
  have e1 := LinearMap.congr_fun h1 (fermionMatterField.repJet U x)
  have e2 := LinearMap.congr_fun (lTensor_fermionProj_repJetGaugeGroupI i U) x
  have e3 := LinearMap.congr_fun
    (GaugeFieldData.lTensor_projFermionValue_repJetFermionModule i U)
    (LinearMap.lTensor JetRing fermionSpaceEquiv.toLinearMap x)
  have e4 := LinearMap.congr_fun h1 x
  simp only [LinearMap.comp_apply] at e1 e2 e3 e4
  -- `show` puts the goal in applied form up to defeq, which `simp only` cannot reach here
  show (LinearMap.lTensor JetRing
        (fieldData.projFermionField 3 fieldData_fermion_massWeight i))
      ((LinearMap.lTensor JetRing fermionSpaceEquiv.toLinearMap)
        (fermionMatterField.repJet U x))
    = (LinearMap.lTensor JetRing
        (fieldData.projFermionField 3 fieldData_fermion_massWeight i))
      (((fieldData.fermionMatterField 3 fieldData_fermion_massWeight).repJet U)
        ((LinearMap.lTensor JetRing fermionSpaceEquiv.toLinearMap) x))
  exact e1.trans (e2.trans ((congrArg _ e4).symm.trans e3.symm))

/-- The relabelling of the Higgs is equivariant for the jet gauge action. There is one
  bosonic species, and reading it off undoes the relabelling, so both sides are the Higgs
  action itself; the content is that the single bosonic species of the datum carries
  exactly the Higgs representation. -/
lemma lTensor_higgsModuleEquiv_repJetGaugeGroupI (U : JetGaugeGroupI) :
    (LinearMap.lTensor JetRing higgsModuleEquiv.toLinearMap).comp
        (HiggsVec.matterField.repJet U)
      = ((fieldData.bosonMatterField 2 fieldData_boson_massWeight).repJet U).comp
        (LinearMap.lTensor JetRing higgsModuleEquiv.toLinearMap) := by
  refine jetPi_hom_ext (fun j => (fieldData.boson j).V) fun j => LinearMap.ext fun z => ?_
  have h1 : ∀ w : JetRing ⊗[ℂ] HiggsVec.matterField.V,
      LinearMap.lTensor JetRing (fieldData.projBosonField 2 fieldData_boson_massWeight j)
        (LinearMap.lTensor JetRing higgsModuleEquiv.toLinearMap w) = w := fun w => by
    induction w using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]; rfl
    | tmul f v => rfl
    | add a b ha hb => rw [map_add, map_add, ha, hb]; rfl
  -- `show` puts the goal in applied form up to defeq, which `simp only` cannot reach here
  show LinearMap.lTensor JetRing (fieldData.projBosonField 2 fieldData_boson_massWeight j)
      ((LinearMap.lTensor JetRing higgsModuleEquiv.toLinearMap)
        (HiggsVec.matterField.repJet U z))
    = LinearMap.lTensor JetRing (fieldData.projBosonField 2 fieldData_boson_massWeight j)
      (((fieldData.bosonMatterField 2 fieldData_boson_massWeight).repJet U)
        ((LinearMap.lTensor JetRing higgsModuleEquiv.toLinearMap) z))
  have e3 : LinearMap.lTensor JetRing
        (fieldData.projBosonField 2 fieldData_boson_massWeight j)
        (((fieldData.bosonMatterField 2 fieldData_boson_massWeight).repJet U)
          ((LinearMap.lTensor JetRing higgsModuleEquiv.toLinearMap) z))
      = ((fieldData.boson j).repJet U)
        (LinearMap.lTensor JetRing (fieldData.projBosonField 2 fieldData_boson_massWeight j)
          ((LinearMap.lTensor JetRing higgsModuleEquiv.toLinearMap) z)) :=
    LinearMap.congr_fun (GaugeFieldData.lTensor_projBosonValue_repJetBosonModule j U) _
  rw [h1, e3, h1]
  -- the one bosonic species is the Higgs, so the two actions are the same
  rfl

/-!

## B. The generator identifications intertwine the transformation data

Nothing in this section is a consequence of transport: the two sides are the generic
species-diagonal structure on the direct sum and the existing Standard Model structure on
the component space of the total target space, and the comparison of the two is what has
content.

### B.1. The Lorentz action

-/

/-- The fermionic generator identification intertwines the Lorentz actions: the
  species-diagonal action of the datum with the Standard Model action on the component
  space of the total fermionic target space. -/
lemma fermionGeneratorsEquiv_repLorentzFermion (Λ : SL(2,ℂ))
    (v : fieldData.FermionGenerators) :
    fermionGeneratorsEquiv (fieldData.repLorentzFermion Λ v)
      = JetComponentSpace.repLorentzGroup fermionMatterField Λ
        (fermionGeneratorsEquiv v) := by
  rw [fermionGeneratorsEquiv, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    JetComponentSpace.comapEquiv_apply, JetComponentSpace.comapEquiv_apply,
    GaugeFieldData.fermionGeneratorsEquiv_repLorentzFermion]
  exact LinearMap.congr_fun
    (JetComponentSpace.comap_comp_repLorentzGroup fermionSpaceEquiv.toLinearMap
      fermionSpaceEquiv_comp_repLorentzGroup Λ) _

/-- The composed form of `fermionGeneratorsEquiv_repLorentzFermion`. -/
lemma fermionGeneratorsEquiv_comp_repLorentzFermion (Λ : SL(2,ℂ)) :
    fermionGeneratorsEquiv.toLinearMap.comp (fieldData.repLorentzFermion Λ)
      = (JetComponentSpace.repLorentzGroup fermionMatterField Λ).comp
        fermionGeneratorsEquiv.toLinearMap :=
  LinearMap.ext fun v => fermionGeneratorsEquiv_repLorentzFermion Λ v

/-- The bosonic generator identification intertwines the Lorentz actions. The Higgs is
  a Lorentz scalar, so both sides act only on the derivative labels; the content is that
  the single bosonic species of the datum carries exactly the trivial Higgs representation
  of the Standard Model. -/
lemma bosonGeneratorsEquiv_repLorentzBoson (Λ : SL(2,ℂ))
    (w : fieldData.BosonGenerators) :
    bosonGeneratorsEquiv (fieldData.repLorentzBoson Λ w)
      = JetComponentSpace.repLorentzGroup HiggsVec.matterField Λ
        (bosonGeneratorsEquiv w) := by
  rw [bosonGeneratorsEquiv, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    JetComponentSpace.comapEquiv_apply, JetComponentSpace.comapEquiv_apply,
    GaugeFieldData.bosonGeneratorsEquiv_repLorentzBoson]
  exact LinearMap.congr_fun
    (JetComponentSpace.comap_comp_repLorentzGroup higgsModuleEquiv.toLinearMap
      higgsModuleEquiv_comp_repLorentzGroup Λ) _

/-- The composed form of `bosonGeneratorsEquiv_repLorentzBoson`. -/
lemma bosonGeneratorsEquiv_comp_repLorentzBoson (Λ : SL(2,ℂ)) :
    bosonGeneratorsEquiv.toLinearMap.comp (fieldData.repLorentzBoson Λ)
      = (JetComponentSpace.repLorentzGroup HiggsVec.matterField
          Λ).comp bosonGeneratorsEquiv.toLinearMap :=
  LinearMap.ext fun w => bosonGeneratorsEquiv_repLorentzBoson Λ w

/-- The inverse form of `fermionGeneratorsEquiv_repLorentzFermion`. -/
lemma fermionGeneratorsEquiv_symm_repLorentzGroup (Λ : SL(2,ℂ))
    (w : JetComponentSpace fermionMatterField) :
    fermionGeneratorsEquiv.symm
        (JetComponentSpace.repLorentzGroup fermionMatterField Λ w)
      = fieldData.repLorentzFermion Λ (fermionGeneratorsEquiv.symm w) :=
  fermionGeneratorsEquiv.injective <|
    (fermionGeneratorsEquiv.apply_symm_apply _).trans <|
      ((congrArg (JetComponentSpace.repLorentzGroup fermionMatterField Λ)
          (fermionGeneratorsEquiv.apply_symm_apply w)).symm.trans
        (fermionGeneratorsEquiv_repLorentzFermion Λ _).symm)

/-- The inverse form of `bosonGeneratorsEquiv_repLorentzBoson`. -/
lemma bosonGeneratorsEquiv_symm_repLorentzGroup (Λ : SL(2,ℂ))
    (w : JetComponentSpace HiggsVec.matterField) :
    bosonGeneratorsEquiv.symm (JetComponentSpace.repLorentzGroup HiggsVec.matterField Λ w)
      = fieldData.repLorentzBoson Λ (bosonGeneratorsEquiv.symm w) :=
  bosonGeneratorsEquiv.injective <|
    (bosonGeneratorsEquiv.apply_symm_apply _).trans <|
      ((congrArg (JetComponentSpace.repLorentzGroup HiggsVec.matterField Λ)
          (bosonGeneratorsEquiv.apply_symm_apply w)).symm.trans
        (bosonGeneratorsEquiv_repLorentzBoson Λ _).symm)

/-!

### B.2. The jet gauge action

Neither half of this is formal. The gauge action mixes a component function with the lower
ones through the Taylor coefficients of the gauge jet, so it sees the derivative label; and
its conjugate half carries `star` of the gauge matrix. Both are covered, at every
derivative label, by `JetComponentSpace.comap_comp_repJet`, whose two halves are proved
separately. The inverse forms below are what the sector algebra equivalences of section C
consume.

-/

/-- The fermionic generator identification intertwines the jet gauge actions: the
  species-diagonal action of the datum with the Standard Model action on the component
  space of the total fermionic target space. No common mass weight is used. -/
lemma fermionGeneratorsEquiv_repJetFermion (U : JetGaugeGroupI)
    (v : fieldData.FermionGenerators) :
    fermionGeneratorsEquiv (fieldData.repJetFermion U v)
      = JetComponentSpace.repJet fermionMatterField U (fermionGeneratorsEquiv v) := by
  rw [fermionGeneratorsEquiv, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    JetComponentSpace.comapEquiv_apply, JetComponentSpace.comapEquiv_apply,
    GaugeFieldData.fermionGeneratorsEquiv_repJetFermion 3 fieldData_fermion_massWeight U v]
  exact LinearMap.congr_fun (JetComponentSpace.comap_comp_repJet
    fermionSpaceEquiv.toLinearMap lTensor_fermionSpaceEquiv_repJetGaugeGroupI U) _

/-- The inverse form of `fermionGeneratorsEquiv_repJetFermion`. -/
lemma fermionGeneratorsEquiv_symm_repJet (U : JetGaugeGroupI)
    (w : JetComponentSpace fermionMatterField) :
    fermionGeneratorsEquiv.symm (JetComponentSpace.repJet fermionMatterField U w)
      = fieldData.repJetFermion U (fermionGeneratorsEquiv.symm w) :=
  fermionGeneratorsEquiv.injective <|
    (fermionGeneratorsEquiv.apply_symm_apply _).trans <|
      ((congrArg (JetComponentSpace.repJet fermionMatterField U)
          (fermionGeneratorsEquiv.apply_symm_apply w)).symm.trans
        (fermionGeneratorsEquiv_repJetFermion U _).symm)

/-- The bosonic generator identification intertwines the jet gauge actions, at the one
  Higgs species. -/
lemma bosonGeneratorsEquiv_repJetBoson (U : JetGaugeGroupI)
    (v : fieldData.BosonGenerators) :
    bosonGeneratorsEquiv (fieldData.repJetBoson U v)
      = JetComponentSpace.repJet HiggsVec.matterField U (bosonGeneratorsEquiv v) := by
  rw [bosonGeneratorsEquiv, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    JetComponentSpace.comapEquiv_apply, JetComponentSpace.comapEquiv_apply,
    GaugeFieldData.bosonGeneratorsEquiv_repJetBoson 2 fieldData_boson_massWeight U v]
  exact LinearMap.congr_fun (JetComponentSpace.comap_comp_repJet
    higgsModuleEquiv.toLinearMap lTensor_higgsModuleEquiv_repJetGaugeGroupI U) _

/-- The inverse form of `bosonGeneratorsEquiv_repJetBoson`. -/
lemma bosonGeneratorsEquiv_symm_repJet (U : JetGaugeGroupI)
    (w : JetComponentSpace HiggsVec.matterField) :
    bosonGeneratorsEquiv.symm (JetComponentSpace.repJet HiggsVec.matterField U w)
      = fieldData.repJetBoson U (bosonGeneratorsEquiv.symm w) :=
  bosonGeneratorsEquiv.injective <|
    (bosonGeneratorsEquiv.apply_symm_apply _).trans <|
      ((congrArg (JetComponentSpace.repJet HiggsVec.matterField U)
          (bosonGeneratorsEquiv.apply_symm_apply w)).symm.trans
        (bosonGeneratorsEquiv_repJetBoson U _).symm)

/-!

### B.3. The mass weights

-/

/-- The fermionic generator identification intertwines the mass-weight scalings: the
  per-species scaling of the datum, which carries the weight three of every Standard Model
  fermion, with the single weight-three scaling of the component space of the total target
  space. That the two agree is exactly the statement that all fifteen species have the same
  weight; the relabelling of the target space costs nothing, the scaling being natural in
  the value space. -/
lemma fermionGeneratorsEquiv_massWeightScaleFermion (c : ℂ)
    (v : fieldData.FermionGenerators) :
    fermionGeneratorsEquiv (fieldData.massWeightScaleFermion c v)
      = JetComponentSpace.massWeightScale 3 c (fermionGeneratorsEquiv v) := by
  rw [fermionGeneratorsEquiv, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    JetComponentSpace.comapEquiv_apply, JetComponentSpace.comapEquiv_apply,
    GaugeFieldData.fermionGeneratorsEquiv_massWeightScaleFermion 3
      fieldData_fermion_massWeight c]
  exact LinearMap.congr_fun
    (JetComponentSpace.comap_comp_massWeightScale fermionSpaceEquiv.toLinearMap 3 c) _

/-- The composed form of `fermionGeneratorsEquiv_massWeightScaleFermion`. -/
lemma fermionGeneratorsEquiv_comp_massWeightScaleFermion (c : ℂ) :
    fermionGeneratorsEquiv.toLinearMap.comp (fieldData.massWeightScaleFermion c)
      = (JetComponentSpace.massWeightScale 3 c).comp
        fermionGeneratorsEquiv.toLinearMap :=
  LinearMap.ext fun v => fermionGeneratorsEquiv_massWeightScaleFermion c v

/-- The bosonic generator identification intertwines the mass-weight scalings, at the
  Higgs weight two. -/
lemma bosonGeneratorsEquiv_massWeightScaleBoson (c : ℂ)
    (w : fieldData.BosonGenerators) :
    bosonGeneratorsEquiv (fieldData.massWeightScaleBoson c w)
      = JetComponentSpace.massWeightScale 2 c (bosonGeneratorsEquiv w) := by
  rw [bosonGeneratorsEquiv, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    JetComponentSpace.comapEquiv_apply, JetComponentSpace.comapEquiv_apply,
    GaugeFieldData.bosonGeneratorsEquiv_massWeightScaleBoson 2
      fieldData_boson_massWeight c]
  exact LinearMap.congr_fun
    (JetComponentSpace.comap_comp_massWeightScale higgsModuleEquiv.toLinearMap 2 c) _

/-- The composed form of `bosonGeneratorsEquiv_massWeightScaleBoson`. -/
lemma bosonGeneratorsEquiv_comp_massWeightScaleBoson (c : ℂ) :
    bosonGeneratorsEquiv.toLinearMap.comp (fieldData.massWeightScaleBoson c)
      = (JetComponentSpace.massWeightScale 2 c).comp bosonGeneratorsEquiv.toLinearMap :=
  LinearMap.ext fun w => bosonGeneratorsEquiv_massWeightScaleBoson c w

/-!

## C. The sector algebra equivalences intertwine the two actions

Each of the two sector algebra equivalences of
`Physlib.Particles.StandardModel.JetAlgebra.SectorEquiv.Basic` is the free-algebra functor
applied to a generator identification, and each of the four actions is the free-algebra
functor applied to an action on the generators. So each statement below is the
corresponding generator statement pushed along an algebra map, by extensionality of algebra
maps on the free algebra — not by induction, unlike the derivative, since a group element
here acts by an algebra homomorphism.

-/

/-- The fermionic sector equivalence intertwines the jet gauge actions. -/
lemma fermionAlgebraEquiv_repJetGaugeGroupI (U : JetGaugeGroupI) (f : FermionJetAlgebra) :
    fermionAlgebraEquiv (FermionJetAlgebra.repJetGaugeGroupI U f)
      = fieldData.repJetFermion.exteriorAlgebra U (fermionAlgebraEquiv f) :=
  ExteriorAlgebra.algHom_exteriorAlgebra fermionAlgebraEquiv.toAlgHom
    (fun x => fermionAlgebraEquiv_ι x) U
    (fun x => fermionGeneratorsEquiv_symm_repJet U x) f

/-- The Higgs sector equivalence intertwines the jet gauge actions. -/
lemma higgsAlgebraEquiv_repJetGaugeGroupI (U : JetGaugeGroupI) (h : HiggsJetAlgebra) :
    higgsAlgebraEquiv (HiggsJetAlgebra.repJetGaugeGroupI U h)
      = fieldData.repJetBoson.symmetricAlgebra U (higgsAlgebraEquiv h) :=
  SymmetricAlgebra.algHom_symmetricAlgebra higgsAlgebraEquiv.toAlgHom
    (fun x => higgsAlgebraEquiv_ι x) U
    (fun x => bosonGeneratorsEquiv_symm_repJet U x) h

/-- The fermionic sector equivalence intertwines the Lorentz actions. -/
lemma fermionAlgebraEquiv_repLorentzGroup (Λ : SL(2,ℂ)) (f : FermionJetAlgebra) :
    fermionAlgebraEquiv (FermionJetAlgebra.repLorentzGroup Λ f)
      = fieldData.repLorentzFermion.exteriorAlgebra Λ (fermionAlgebraEquiv f) :=
  ExteriorAlgebra.algHom_exteriorAlgebra fermionAlgebraEquiv.toAlgHom
    (fun x => fermionAlgebraEquiv_ι x) Λ
    (fun x => fermionGeneratorsEquiv_symm_repLorentzGroup Λ x) f

/-- The Higgs sector equivalence intertwines the Lorentz actions. -/
lemma higgsAlgebraEquiv_repLorentzGroup (Λ : SL(2,ℂ)) (h : HiggsJetAlgebra) :
    higgsAlgebraEquiv (HiggsJetAlgebra.repLorentzGroup Λ h)
      = fieldData.repLorentzBoson.symmetricAlgebra Λ (higgsAlgebraEquiv h) :=
  SymmetricAlgebra.algHom_symmetricAlgebra higgsAlgebraEquiv.toAlgHom
    (fun x => higgsAlgebraEquiv_ι x) Λ
    (fun x => bosonGeneratorsEquiv_symm_repLorentzGroup Λ x) h

end StandardModel
