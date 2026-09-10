/-
Copyright (c) 2026 Nathaneal Sajan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaneal Sajan
-/
module

public import Physlib.ClassicalFieldTheory.GaugeTheory.MatterField.Basic
public import Physlib.Particles.StandardModel.Fermions.DownSinglet.GaugeAlgebraAction
public import Physlib.Particles.StandardModel.GaugeGroup.LocalGaugeData
public import Physlib.Particles.StandardModel.Fermions.LeptonDoublet.GaugeAlgebraAction
public import Physlib.Particles.StandardModel.Fermions.LeptonSinglet.GaugeAlgebraAction
public import Physlib.Particles.StandardModel.Fermions.QuarkDoublet.GaugeAlgebraAction
public import Physlib.Particles.StandardModel.Fermions.UpSinglet.GaugeAlgebraAction
/-!
# The Standard Model fermions as matter fields

## i. Overview

`MatterField jets` bundles the value space of one field of a gauge theory over a gauge
context `jets`, its Lorentz representation, the fibrewise action of the jets of gauge
transformations on the jets of the field, and its mass weight. The five Standard Model
fermion types already carry all four, and this file collects them. Nothing is redefined
and no convention is changed. The chirality, the gauge representation, the hypercharge
normalization `6Y` and the fibrewise-linearity proof are the ones already in the species
files.

There is one adapter per fermion type, not per type and generation, since `FermionSpace`
carries `Fin 3` copies of each type and a matter field describes one multiplet.

Mass weight three is the fermionic weight already fixed by
`FermionJetAlgebra.massWeightScale`, in the units in which a derivative has weight two.

## ii. Key results

- `StandardModel.LeptonDoublet.matterField` : the lepton doublet as a matter field.
- `StandardModel.LeptonSinglet.matterField` : the charged-lepton singlet as a matter field.
- `StandardModel.QuarkDoublet.matterField` : the quark doublet as a matter field.
- `StandardModel.UpSinglet.matterField` : the up-type singlet as a matter field.
- `StandardModel.DownSinglet.matterField` : the down-type singlet as a matter field.

Each comes with the four projection rules `…matterField_V`, `…matterField_repLorentz`,
`…matterField_repJet` and `…matterField_massWeight` identifying its fields with the
existing Standard Model definitions.

## iii. Table of contents

- A. The lepton sector
  - A.1. The lepton doublet
  - A.2. The charged-lepton singlet
- B. The quark sector
  - B.1. The quark doublet
  - B.2. The up-type singlet
  - B.3. The down-type singlet

-/

@[expose] public section

namespace StandardModel

/-!

## A. The lepton sector

### A.1. The lepton doublet

-/

namespace LeptonDoublet

/-- The lepton doublet as a matter field of `StandardModel.localGaugeData`, in the `(1, 2)_{-3}`
  representation with its left-handed Lorentz action. -/
noncomputable def matterField : MatterField localGaugeData where
  V := LeptonDoublet
  repLorentz := repLorentzGroup
  repJet := repJetGaugeGroupI
  repAlgebra := gaugeAlgebraAction
  repAlgebra_isInfinitesimalAction := isInfinitesimalActionOf
  repJet_smul := repJetGaugeGroupI_smul
  massWeight := 3

@[simp]
lemma matterField_V : matterField.V = LeptonDoublet := rfl

@[simp]
lemma matterField_repLorentz : matterField.repLorentz = repLorentzGroup := rfl

@[simp]
lemma matterField_repJet : matterField.repJet = repJetGaugeGroupI := rfl

@[simp]
lemma matterField_repAlgebra : matterField.repAlgebra = gaugeAlgebraAction := rfl

@[simp]
lemma matterField_massWeight : matterField.massWeight = 3 := rfl

end LeptonDoublet

/-!

### A.2. The charged-lepton singlet

-/

namespace LeptonSinglet

/-- The charged-lepton singlet as a matter field of `StandardModel.localGaugeData`, in the
  `(1, 1)_{-6}` representation with its right-handed Lorentz action. -/
noncomputable def matterField : MatterField localGaugeData where
  V := LeptonSinglet
  repLorentz := repLorentzGroup
  repJet := repJetGaugeGroupI
  repAlgebra := gaugeAlgebraAction
  repAlgebra_isInfinitesimalAction := isInfinitesimalActionOf
  repJet_smul := repJetGaugeGroupI_smul
  massWeight := 3

@[simp]
lemma matterField_V : matterField.V = LeptonSinglet := rfl

@[simp]
lemma matterField_repLorentz : matterField.repLorentz = repLorentzGroup := rfl

@[simp]
lemma matterField_repJet : matterField.repJet = repJetGaugeGroupI := rfl

@[simp]
lemma matterField_repAlgebra : matterField.repAlgebra = gaugeAlgebraAction := rfl

@[simp]
lemma matterField_massWeight : matterField.massWeight = 3 := rfl

end LeptonSinglet

/-!

## B. The quark sector

### B.1. The quark doublet

-/

namespace QuarkDoublet

/-- The quark doublet as a matter field of `StandardModel.localGaugeData`, in the `(3, 2)_{1}`
  representation with its left-handed Lorentz action. -/
noncomputable def matterField : MatterField localGaugeData where
  V := QuarkDoublet
  repLorentz := repLorentzGroup
  repJet := repJetGaugeGroupI
  repAlgebra := gaugeAlgebraAction
  repAlgebra_isInfinitesimalAction := isInfinitesimalActionOf
  repJet_smul := repJetGaugeGroupI_smul
  massWeight := 3

@[simp]
lemma matterField_V : matterField.V = QuarkDoublet := rfl

@[simp]
lemma matterField_repLorentz : matterField.repLorentz = repLorentzGroup := rfl

@[simp]
lemma matterField_repJet : matterField.repJet = repJetGaugeGroupI := rfl

@[simp]
lemma matterField_repAlgebra : matterField.repAlgebra = gaugeAlgebraAction := rfl

@[simp]
lemma matterField_massWeight : matterField.massWeight = 3 := rfl

end QuarkDoublet

/-!

### B.2. The up-type singlet

-/

namespace UpSinglet

/-- The up-type quark singlet as a matter field of `StandardModel.localGaugeData`, in the
  `(3, 1)_{4}` representation with its right-handed Lorentz action. -/
noncomputable def matterField : MatterField localGaugeData where
  V := UpSinglet
  repLorentz := repLorentzGroup
  repJet := repJetGaugeGroupI
  repAlgebra := gaugeAlgebraAction
  repAlgebra_isInfinitesimalAction := isInfinitesimalActionOf
  repJet_smul := repJetGaugeGroupI_smul
  massWeight := 3

@[simp]
lemma matterField_V : matterField.V = UpSinglet := rfl

@[simp]
lemma matterField_repLorentz : matterField.repLorentz = repLorentzGroup := rfl

@[simp]
lemma matterField_repJet : matterField.repJet = repJetGaugeGroupI := rfl

@[simp]
lemma matterField_repAlgebra : matterField.repAlgebra = gaugeAlgebraAction := rfl

@[simp]
lemma matterField_massWeight : matterField.massWeight = 3 := rfl

end UpSinglet

/-!

### B.3. The down-type singlet

-/

namespace DownSinglet

/-- The down-type quark singlet as a matter field of `StandardModel.localGaugeData`, in the
  `(3, 1)_{-2}` representation with its right-handed Lorentz action. -/
noncomputable def matterField : MatterField localGaugeData where
  V := DownSinglet
  repLorentz := repLorentzGroup
  repJet := repJetGaugeGroupI
  repAlgebra := gaugeAlgebraAction
  repAlgebra_isInfinitesimalAction := isInfinitesimalActionOf
  repJet_smul := repJetGaugeGroupI_smul
  massWeight := 3

@[simp]
lemma matterField_V : matterField.V = DownSinglet := rfl

@[simp]
lemma matterField_repLorentz : matterField.repLorentz = repLorentzGroup := rfl

@[simp]
lemma matterField_repJet : matterField.repJet = repJetGaugeGroupI := rfl

@[simp]
lemma matterField_repAlgebra : matterField.repAlgebra = gaugeAlgebraAction := rfl

@[simp]
lemma matterField_massWeight : matterField.massWeight = 3 := rfl

end DownSinglet

end StandardModel
