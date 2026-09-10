/-
Copyright (c) 2026 Nathaneal Sajan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaneal Sajan
-/
module

public import Physlib.ClassicalFieldTheory.JetAlgebra.LocalFieldAlgebra
public import Physlib.Particles.StandardModel.Fermions.MatterField
public import Physlib.Particles.StandardModel.GaugeGroup.LocalGaugeData
public import Physlib.Particles.StandardModel.HiggsBoson.MatterField
/-!
# The field data of the Standard Model

## i. Overview

`GaugeFieldData jets` is the matter content of a gauge theory over a gauge context: a
family of fermionic species and a family of bosonic species, each given by a
`MatterField`. The Standard Model has all the pieces — `StandardModel.localGaugeData` with its
Taylor–Leibniz law, and the five fermion types and the Higgs already packaged as matter
fields — and this file assembles them into `StandardModel.fieldData`.

The fermionic species are the constructors of `FermionType`: fifteen multiplets, one of
the five types in one of the three generations, each occurring exactly once. The
generation index is an argument of each constructor, so the species type is the
enumeration itself and carries no further factor. The matter field does not depend on the
generation, three generations being three copies of one multiplet distinguished only by
their Yukawa couplings, which are not field data. The bosonic family has the single Higgs
multiplet. The gauge bosons are not a species: their generator space is fixed by the gauge
algebra alone, and `GaugeFieldData` supplies it as the connection sector.

From the datum the generic theory produces the generator spaces, the local field algebra
`fieldData.LocalFieldAlgebra`, the transformation data and the realization arrow, with no
further Standard Model input.

## ii. Key results

- `StandardModel.FermionType` : the fifteen fermion species, the five types in each of
  the three generations.
- `StandardModel.fieldData` : the field data of the Standard Model.
- `StandardModel.card_fieldData_fermionSpecies`,
  `StandardModel.card_fieldData_bosonSpecies` : fifteen fermionic multiplets, one Higgs.
- `StandardModel.fieldData_massWeightScaleFermion_inclFermion_basis_tmul` : a fermionic
  component function `∂_s ψ_α` scales by `c ^ (3 + 2 |s|)`.

## iii. Table of contents

- A. The fermion species
- B. The field datum
- C. The mass weights

-/

@[expose] public section

open TensorProduct

namespace StandardModel

/-!

## A. The fermion species

-/

/-- The fifteen fermion species of the Standard Model: each of the five fermion types in
  each of the three generations, the generation `i : Fin 3` carried by the constructor.
  Two generations of one type share a representation package but are distinct species. -/
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

/-- The matter field of a fermion species, one of the five existing adapters. It is the
  same in every generation. -/
noncomputable def matterField : FermionType → MatterField localGaugeData
  | .leptonDoublet _ => LeptonDoublet.matterField
  | .leptonSinglet _ => LeptonSinglet.matterField
  | .quarkDoublet _ => QuarkDoublet.matterField
  | .upSinglet _ => UpSinglet.matterField
  | .downSinglet _ => DownSinglet.matterField

@[simp]
lemma matterField_leptonDoublet (i : Fin 3) :
    matterField (.leptonDoublet i) = LeptonDoublet.matterField := rfl

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

end FermionType

/-!

## B. The field datum

-/

/-- The field data of the Standard Model: three generations of each of the five fermion
  types and one Higgs multiplet, over the gauge context `StandardModel.localGaugeData`. -/
noncomputable def fieldData : GaugeFieldData localGaugeData where
  FermionSpecies := FermionType
  fermion := FermionType.matterField
  BosonSpecies := Unit
  boson := fun _ => HiggsVec.matterField

@[simp]
lemma fieldData_fermionSpecies : fieldData.FermionSpecies = FermionType := rfl

/-- A fermionic species is the multiplet of its type, whichever generation it is in. -/
@[simp]
lemma fieldData_fermion (t : FermionType) : fieldData.fermion t = t.matterField := rfl

@[simp]
lemma fieldData_bosonSpecies : fieldData.BosonSpecies = Unit := rfl

/-- The one bosonic species is the Higgs multiplet. -/
@[simp]
lemma fieldData_boson (j : fieldData.BosonSpecies) :
    fieldData.boson j = HiggsVec.matterField := rfl

/-- Fifteen fermionic multiplets: each of the five types in each of the three
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

## C. The mass weights

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
        ((DerivAlgebraComplex.basis s ⊗ₜ[ℂ] φ, 0) :
          JetComponentSpace (fieldData.FermionValue j)))
      = c ^ (3 + 2 * Multiset.card s) • fieldData.inclFermion j
          ((DerivAlgebraComplex.basis s ⊗ₜ[ℂ] φ, 0) :
            JetComponentSpace (fieldData.FermionValue j)) := by
  have h := GaugeFieldData.massWeightScaleFermion_inclFermion_basis_tmul
    (T := fieldData) c j s φ
  rwa [fieldData_fermion_massWeight] at h

/-- A Higgs component function `∂_s H_α` scales by `c ^ (2 + 2 |s|)`. -/
lemma fieldData_massWeightScaleBoson_inclBoson_basis_tmul (c : ℂ)
    (j : fieldData.BosonSpecies) (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (fieldData.BosonValue j)) :
    fieldData.massWeightScaleBoson c (fieldData.inclBoson j
        ((DerivAlgebraComplex.basis s ⊗ₜ[ℂ] φ, 0) :
          JetComponentSpace (fieldData.BosonValue j)))
      = c ^ (2 + 2 * Multiset.card s) • fieldData.inclBoson j
          ((DerivAlgebraComplex.basis s ⊗ₜ[ℂ] φ, 0) :
            JetComponentSpace (fieldData.BosonValue j)) := by
  have h := GaugeFieldData.massWeightScaleBoson_inclBoson_basis_tmul
    (T := fieldData) c j s φ
  rwa [fieldData_boson_massWeight] at h

end StandardModel
