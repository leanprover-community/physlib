/-
Copyright (c) 2026 Nathaneal Sajan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaneal Sajan
-/
module

public import Physlib.ClassicalFieldTheory.GaugeTheory.MatterField.Basic
public import Physlib.Particles.StandardModel.GaugeGroup.LocalGaugeData
public import Physlib.Particles.StandardModel.HiggsBoson.GaugeAlgebraAction
public import Physlib.Particles.StandardModel.HiggsBoson.JetAlgebra.Basic
/-!
# The Standard Model Higgs field as a matter field

## i. Overview

`MatterField jets` bundles the value space of one field of a gauge theory over a gauge
context `jets`, its Lorentz representation, the fibrewise action of the jets of gauge
transformations, and its mass weight. The Higgs already carries all four, and this file
collects them, as `Physlib.Particles.StandardModel.Fermions.MatterField` does for the five
fermion types. Nothing is redefined and no convention is changed: the `2_{3}` jet action
and its fibrewise-linearity proof are the ones in
`Physlib.Particles.StandardModel.HiggsBoson.JetAlgebra.Basic`, the Higgs is a Lorentz
scalar, and mass weight two is the weight already fixed by
`HiggsJetAlgebra.massWeightScale`.

## ii. Key results

- `StandardModel.HiggsVec.matterField` : the Higgs field as a matter field, with the four
  projection rules identifying its fields with the existing definitions.

## iii. Table of contents

- A. The Higgs as a matter field

-/

@[expose] public section

open Matrix MatrixGroups

namespace StandardModel

namespace HiggsVec

/-!

## A. The Higgs as a matter field

-/

/-- The Higgs field as a matter field of `StandardModel.localGaugeData`, valued in
  `HiggsVec`, in the `2_{3}` representation of the gauge group, a Lorentz scalar, of mass
  weight two. -/
noncomputable def matterField : MatterField localGaugeData where
  V := HiggsVec
  repLorentz := Representation.trivial ℂ SL(2,ℂ) HiggsVec
  repJet := repJetGaugeGroupI
  repAlgebra := gaugeAlgebraAction
  repAlgebra_isInfinitesimalAction := isInfinitesimalActionOf
  repJet_smul := repJetGaugeGroupI_smul
  massWeight := 2

@[simp]
lemma matterField_V : matterField.V = HiggsVec := rfl

@[simp]
lemma matterField_repLorentz :
    matterField.repLorentz = Representation.trivial ℂ SL(2,ℂ) HiggsVec := rfl

@[simp]
lemma matterField_repJet : matterField.repJet = repJetGaugeGroupI := rfl

@[simp]
lemma matterField_repAlgebra : matterField.repAlgebra = gaugeAlgebraAction := rfl

@[simp]
lemma matterField_massWeight : matterField.massWeight = 2 := rfl

end HiggsVec

end StandardModel
