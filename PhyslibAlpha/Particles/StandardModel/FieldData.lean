/-
Copyright (c) 2026 Nathaneal Sajan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.LocalFieldAlgebra.Basic
public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.LocalFieldAlgebra.MassWeight
public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.LocalFieldAlgebra.Realization.Basic
public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.LocalFieldAlgebra.Realization.Conditions
public import PhyslibAlpha.Particles.StandardModel.Fermions.DownSinglet.GaugeAlgebraAction
public import PhyslibAlpha.Particles.StandardModel.Fermions.LeptonDoublet.GaugeAlgebraAction
public import PhyslibAlpha.Particles.StandardModel.Fermions.LeptonSinglet.GaugeAlgebraAction
public import PhyslibAlpha.Particles.StandardModel.Fermions.QuarkDoublet.GaugeAlgebraAction
public import PhyslibAlpha.Particles.StandardModel.Fermions.UpSinglet.GaugeAlgebraAction
public import PhyslibAlpha.Particles.StandardModel.HiggsBoson.GaugeAlgebraAction
/-!
# The field data of the Standard Model

The fifteen fermion species and the Higgs as the field data over the Standard Model global
gauge group, with their conditions and mass weights.

## i. Overview

`GaugeFieldData G` is the matter content of a gauge theory over a global gauge group `G`, a
family of fermionic species and a family of bosonic species, each given by a
`MatterField`. The Standard Model has all the pieces, the global gauge group
`StandardModel.globalGaugeGroup` and the five fermion types and the Higgs already packaged as
matter fields, and this file assembles them into `StandardModel.fieldData`.

The fermionic species are the constructors of `FermionType`, fifteen multiplets, one of
the five types in one of the three generations, each occurring exactly once. The
generation index is an argument of each constructor, so the species type is the
enumeration itself and carries no further factor. The matter field does not depend on the
generation, three generations being three copies of one multiplet distinguished only by
their Yukawa couplings, which are not field data. The bosonic family has the single Higgs
multiplet. The fermions are declared fermionic and the Higgs bosonic, as `GaugeFieldData`
requires of its two families. The gauge bosons are not a species. Their generator space is
fixed by the gauge algebra alone, and `GaugeFieldData` supplies it as the connection sector.

From the datum the generic theory produces the generator spaces, the local field algebra
`fieldData.LocalFieldAlgebra`, the transformation data and the realization arrow, with no
further Standard Model input.

## ii. Key results

- `StandardModel.FermionType` : the fifteen fermion species, the five types in each of
  the three generations.
- `StandardModel.fieldData` : the field data of the Standard Model.
- `StandardModel.card_fieldData_fermionSpecies`,
  `StandardModel.card_fieldData_bosonSpecies` : fifteen fermionic multiplets, one Higgs.
- `StandardModel.fieldData_lorentzContinuous`, `StandardModel.fieldData_gaugeLorentzCommute` :
  the Lorentz representations are continuous and commute with the gauge representations.
- `StandardModel.fieldData_gaugeLorentzCompatible` : the datum satisfies the condition
  of the covariant derivative theory, derived from `StandardModel.fieldData_gaugeLorentzCommute`.
- `StandardModel.fieldData_mem_invariants_iff_exists_mem_invariants` : the invariants of any
  realization of the local field algebra of the Standard Model are the images of the invariants
  of its covariant field algebra.
- `StandardModel.fieldData_massWeightScaleFermion_inclFermion_basis_tmul`,
  `StandardModel.fieldData_massWeightScaleBoson_inclBoson_basis_tmul` : a fermionic component
  function `∂_s ψ_α` scales by `c ^ (3 + 2 |s|)`, a Higgs component by `c ^ (2 + 2 |s|)`.
- `StandardModel.massWeightPoly_fieldData_fermionSymbol`,
  `StandardModel.massWeightPoly_fieldData_bosonSymbol` and their conjugates : the fermion
  symbols have mass weight `3 + 2 |s|`, the Higgs symbols `2 + 2 |s|`.

## iii. Table of contents

- A. The fermion species
- B. The field datum
- C. The conditions on the species
- D. The mass weights

## iv. References

* None.

-/

@[expose] public section

open TensorProduct MatrixGroups

namespace StandardModel

/-!

## A. The fermion species

-/

/-- The fifteen fermion species of the Standard Model, each of the five fermion types in
  each of the three generations, the generation `i : Fin 3` carried by the constructor.
  Two generations of one type share a matter field but are distinct species. -/
inductive FermionType where
  /-- The lepton doublet of generation `i`, `(1, 2)_{-3}`. -/
  | leptonDoublet (i : Fin 3) : FermionType
  /-- The charged-lepton singlet of generation `i`, `(1, 1)_{-6}`. -/
  | leptonSinglet (i : Fin 3) : FermionType
  /-- The quark doublet of generation `i`, `(3, 2)_{1}`. -/
  | quarkDoublet (i : Fin 3) : FermionType
  /-- The up-type quark singlet of generation `i`, `(3, 1)_{4}`. -/
  | upSinglet (i : Fin 3) : FermionType
  /-- The down-type quark singlet of generation `i`, `(3, 1)_{-2}`. -/
  | downSinglet (i : Fin 3) : FermionType

deriving DecidableEq, Fintype

namespace FermionType

/-- The matter field of a fermion species, that of its type. It is the same in every
  generation. -/
noncomputable def matterField : FermionType → globalGaugeGroup.MatterField
  | .leptonDoublet _ => LeptonDoubletV.matterField
  | .leptonSinglet _ => LeptonSinglet.matterField
  | .quarkDoublet _ => QuarkDoublet.matterField
  | .upSinglet _ => UpSinglet.matterField
  | .downSinglet _ => DownSinglet.matterField

@[simp]
lemma matterField_leptonDoublet (i : Fin 3) :
    matterField (.leptonDoublet i) = LeptonDoubletV.matterField := rfl

@[simp]
lemma matterField_leptonSinglet (i : Fin 3) :
    matterField (.leptonSinglet i) = LeptonSinglet.matterField := rfl

@[simp]
lemma matterField_quarkDoublet (i : Fin 3) :
    matterField (.quarkDoublet i) = QuarkDoublet.matterField := rfl

@[simp]
lemma matterField_upSinglet (i : Fin 3) :
    matterField (.upSinglet i) = UpSinglet.matterField := rfl

@[simp]
lemma matterField_downSinglet (i : Fin 3) :
    matterField (.downSinglet i) = DownSinglet.matterField := rfl

/-- Every Standard Model fermion carries mass weight three, in every generation. -/
@[simp]
lemma matterField_massWeight (t : FermionType) : (matterField t).massWeight = 3 := by
  cases t <;> rfl

/-- Every Standard Model fermion is declared fermionic, in every generation. -/
@[simp]
lemma matterField_statistic (t : FermionType) : (matterField t).statistic = .fermionic := by
  cases t <;> rfl

end FermionType

/-!

## B. The field datum

-/

/-- The field data of the Standard Model, three generations of each of the five fermion
  types and one Higgs multiplet, over the global gauge group `StandardModel.globalGaugeGroup`. -/
noncomputable def fieldData : GaugeFieldData globalGaugeGroup where
  FermionSpecies := FermionType
  fermion := FermionType.matterField
  fermion_statistic := FermionType.matterField_statistic
  BosonSpecies := Unit
  boson := fun _ => HiggsVec.matterField
  boson_statistic _ := rfl

/-- The fermionic species are the fifteen fermion types. -/
@[simp]
lemma fieldData_fermionSpecies : fieldData.FermionSpecies = FermionType := rfl

/-- A fermionic species is the multiplet of its type, whichever generation it is in. -/
@[simp]
lemma fieldData_fermion (t : FermionType) : fieldData.fermion t = t.matterField := rfl

/-- There is one bosonic species. -/
@[simp]
lemma fieldData_bosonSpecies : fieldData.BosonSpecies = Unit := rfl

/-- The one bosonic species is the Higgs multiplet. -/
@[simp]
lemma fieldData_boson (j : fieldData.BosonSpecies) :
    fieldData.boson j = HiggsVec.matterField := rfl

/-- There are fifteen fermionic multiplets, each of the five types in each of the three
  generations, exactly once. -/
lemma card_fieldData_fermionSpecies : Nat.card fieldData.FermionSpecies = 15 := by
  show Nat.card FermionType = 15
  rw [Nat.card_eq_fintype_card]
  rfl

/-- Exactly one bosonic multiplet, the Higgs. -/
lemma card_fieldData_bosonSpecies : Nat.card fieldData.BosonSpecies = 1 := by
  show Nat.card Unit = 1
  simp

/-!

## C. The conditions on the species

The global gauge group of the Standard Model is compact, and on every species the Lorentz
representation is continuous and commutes with the gauge representation. These are the
hypotheses under which the invariants of a realization of the local field algebra descend to
the covariant field algebra. The commutation implies its infinitesimal form
`GaugeFieldData.GaugeLorentzCompatible`, the condition of the covariant derivative theory.

-/

/-- The Lorentz action on every fermionic species of the Standard Model is continuous. -/
lemma fieldData_fermion_lorentzContinuous (t : FermionType) :
    (fieldData.fermion t).LorentzContinuous := by
  cases t
  · exact LeptonDoubletV.matterField_lorentzContinuous
  · exact LeptonSinglet.matterField_lorentzContinuous
  · exact QuarkDoublet.matterField_lorentzContinuous
  · exact UpSinglet.matterField_lorentzContinuous
  · exact DownSinglet.matterField_lorentzContinuous

/-- The Lorentz action on every species of the Standard Model is continuous. -/
lemma fieldData_lorentzContinuous : fieldData.LorentzContinuous :=
  ⟨fieldData_fermion_lorentzContinuous, fun _ => HiggsVec.matterField_lorentzContinuous⟩

/-- The gauge and Lorentz representations of every fermionic species of the Standard Model
  commute. -/
lemma fieldData_fermion_gaugeLorentzCommute (t : FermionType) :
    (fieldData.fermion t).GaugeLorentzCommute := by
  cases t
  · exact LeptonDoubletV.matterField_gaugeLorentzCommute
  · exact LeptonSinglet.matterField_gaugeLorentzCommute
  · exact QuarkDoublet.matterField_gaugeLorentzCommute
  · exact UpSinglet.matterField_gaugeLorentzCommute
  · exact DownSinglet.matterField_gaugeLorentzCommute

/-- The gauge and Lorentz representations of every species of the Standard Model commute. -/
lemma fieldData_gaugeLorentzCommute : fieldData.GaugeLorentzCommute :=
  ⟨fieldData_fermion_gaugeLorentzCommute, fun _ => HiggsVec.matterField_gaugeLorentzCommute⟩

/-- The infinitesimal gauge action commutes with the Lorentz action on every species of the
  Standard Model. -/
lemma fieldData_gaugeLorentzCompatible : fieldData.GaugeLorentzCompatible :=
  fieldData_gaugeLorentzCommute.gaugeLorentzCompatible

/-- The invariants of a realization of the local field algebra of the Standard Model are the
  images of the invariants of its covariant field algebra. An element `k x` is invariant under
  the jet gauge group and the Lorentz group exactly when it is the image of a covariant
  expression invariant under the ordinary gauge group and the Lorentz group. -/
lemma fieldData_mem_invariants_iff_exists_mem_invariants {B : Type} [Ring B] [Algebra ℂ B]
    {repJet : Representation ℂ globalGaugeGroup.gaugeJetGroup B}
    {repLorentz : Representation ℂ SL(2,ℂ) B}
    (k : GaugeFieldData.Realization fieldData B repJet repLorentz)
    (x : fieldData.LocalFieldAlgebra) :
    k.toAlgHom x ∈ repJet.invariants ∧ k.toAlgHom x ∈ repLorentz.invariants ↔
      ∃ a' : fieldData.LocalCovFieldAlgebra,
        a' ∈ (GaugeFieldData.LocalCovFieldAlgebra.repValue fieldData).invariants ∧
        a' ∈ (GaugeFieldData.LocalCovFieldAlgebra.repLorentzGroup fieldData
          fieldData_gaugeLorentzCompatible).invariants ∧
        k.toAlgHom (a' : fieldData.LocalFieldAlgebra) = k.toAlgHom x :=
  k.mem_invariants_iff_exists_mem_invariants fieldData_lorentzContinuous
    fieldData_gaugeLorentzCommute x

/-!

## D. The mass weights

A Standard Model fermion carries mass weight three and the Higgs weight two, in the units
in which a derivative has weight two. The first two are read off the matter fields, the
third is already built into the generator spaces.

-/

/-- Every fermionic species of the datum carries mass weight three. -/
@[simp]
lemma fieldData_fermion_massWeight (j : fieldData.FermionSpecies) :
    (fieldData.fermion j).massWeight = 3 :=
  FermionType.matterField_massWeight j

/-- The Higgs multiplet carries mass weight two. -/
@[simp]
lemma fieldData_boson_massWeight (j : fieldData.BosonSpecies) :
    (fieldData.boson j).massWeight = 2 := rfl

/-- A fermionic component function `∂_s ψ_α` scales by `c ^ (3 + 2 |s|)`, whichever
  species it belongs to. -/
lemma fieldData_massWeightScaleFermion_inclFermion_basis_tmul (c : ℂ)
    (j : fieldData.FermionSpecies) (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (fieldData.FermionValue j)) :
    fieldData.massWeightScaleFermion c (fieldData.inclFermion j
        ((SpaceTimeDerivAlgebraℂ.basis s ⊗ₜ[ℂ] φ, 0) :
          FieldDerivSpace (fieldData.fermion j)))
      = c ^ (3 + 2 * Multiset.card s) • fieldData.inclFermion j
          ((SpaceTimeDerivAlgebraℂ.basis s ⊗ₜ[ℂ] φ, 0) :
            FieldDerivSpace (fieldData.fermion j)) := by
  have h := GaugeFieldData.massWeightScaleFermion_inclFermion_basis_tmul
    (T := fieldData) c j s φ
  rwa [fieldData_fermion_massWeight] at h

/-- A Higgs component function `∂_s H_α` scales by `c ^ (2 + 2 |s|)`. -/
lemma fieldData_massWeightScaleBoson_inclBoson_basis_tmul (c : ℂ)
    (j : fieldData.BosonSpecies) (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (fieldData.BosonValue j)) :
    fieldData.massWeightScaleBoson c (fieldData.inclBoson j
        ((SpaceTimeDerivAlgebraℂ.basis s ⊗ₜ[ℂ] φ, 0) :
          FieldDerivSpace (fieldData.boson j)))
      = c ^ (2 + 2 * Multiset.card s) • fieldData.inclBoson j
          ((SpaceTimeDerivAlgebraℂ.basis s ⊗ₜ[ℂ] φ, 0) :
            FieldDerivSpace (fieldData.boson j)) := by
  have h := GaugeFieldData.massWeightScaleBoson_inclBoson_basis_tmul
    (T := fieldData) c j s φ
  rwa [fieldData_boson_massWeight] at h

/-- The symbols of every fermionic species of the field datum have mass weight
  `3 + 2 |s|`, every fermion having mass dimension `3/2`. -/
lemma massWeightPoly_fieldData_fermionSymbol (t : FermionType) (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (fieldData.FermionValue t)) :
    fieldData.massWeightPoly (fieldData.fermionSymbol t s φ)
      = Polynomial.monomial (3 + 2 * Multiset.card s) (fieldData.fermionSymbol t s φ) :=
  (GaugeFieldData.massWeightPoly_fermionSymbol (T := fieldData) t s φ).trans
    (congrArg (fun n => Polynomial.monomial (n + 2 * Multiset.card s)
      (fieldData.fermionSymbol t s φ)) (fieldData_fermion_massWeight t))

/-- The conjugate symbols of every fermionic species of the field datum have mass weight
  `3 + 2 |s|`. -/
lemma massWeightPoly_fieldData_conjFermionSymbol (t : FermionType)
    (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (ConjModule (fieldData.FermionValue t))) :
    fieldData.massWeightPoly (fieldData.conjFermionSymbol t s φ)
      = Polynomial.monomial (3 + 2 * Multiset.card s) (fieldData.conjFermionSymbol t s φ) :=
  (GaugeFieldData.massWeightPoly_conjFermionSymbol (T := fieldData) t s φ).trans
    (congrArg (fun n => Polynomial.monomial (n + 2 * Multiset.card s)
      (fieldData.conjFermionSymbol t s φ)) (fieldData_fermion_massWeight t))

/-- The symbols of the Higgs, the one bosonic species of the field datum, have mass weight
  `2 + 2 |s|`, the Higgs field having mass dimension one. -/
lemma massWeightPoly_fieldData_bosonSymbol (j : fieldData.BosonSpecies)
    (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (fieldData.BosonValue j)) :
    fieldData.massWeightPoly (fieldData.bosonSymbol j s φ)
      = Polynomial.monomial (2 + 2 * Multiset.card s) (fieldData.bosonSymbol j s φ) :=
  (GaugeFieldData.massWeightPoly_bosonSymbol (T := fieldData) j s φ).trans
    (congrArg (fun n => Polynomial.monomial (n + 2 * Multiset.card s)
      (fieldData.bosonSymbol j s φ)) (fieldData_boson_massWeight j))

/-- The conjugate symbols of the Higgs have mass weight `2 + 2 |s|`. -/
lemma massWeightPoly_fieldData_conjBosonSymbol (j : fieldData.BosonSpecies)
    (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (ConjModule (fieldData.BosonValue j))) :
    fieldData.massWeightPoly (fieldData.conjBosonSymbol j s φ)
      = Polynomial.monomial (2 + 2 * Multiset.card s) (fieldData.conjBosonSymbol j s φ) :=
  (GaugeFieldData.massWeightPoly_conjBosonSymbol (T := fieldData) j s φ).trans
    (congrArg (fun n => Polynomial.monomial (n + 2 * Multiset.card s)
      (fieldData.conjBosonSymbol j s φ)) (fieldData_boson_massWeight j))

end StandardModel
