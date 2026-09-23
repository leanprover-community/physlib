/-
Copyright (c) 2026 Jinzheng Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li
-/
module

public import Physlib.Particles.StandardModel.Basic
public import Physlib.Particles.StandardModel.Fermions.MatterField
/-!

# The lepton doublet of the Standard Model table

## i. Overview

The lepton doublet of the Standard Model is the datum `StandardModel.Model.leptonDoublet`,
`(.L, .singlet, .fund, -3)`, of `Physlib.Particles.StandardModel.Basic`. The species
`StandardModel.LeptonDoublet` is its target space, and the species' weak matrix, action
matrix, Lorentz, global gauge, jet and gauge-algebra actions and matter field are the ones
the general theory derives from the datum. This file records the identities, all of which
hold by definition.

## ii. Key results

- `StandardModel.Model.leptonDoublet_toMatterField_eq` : the matter field of the datum is
  `LeptonDoublet.matterField`.

-/

@[expose] public section

open LocalGaugeData

namespace StandardModel

namespace Model

/-- The lepton doublet is indexed by a weak index alone. -/
example : leptonDoublet.Idx = Fin 2 := rfl

/-- The lepton doublet has mass weight `3`. -/
example : leptonDoublet.massWeight = 3 := rfl

/-- The weak matrix of the species is the matrix of jets of the datum. -/
example (U : JetGaugeGroupI) : leptonDoublet.rep.mat U = LeptonDoublet.doubletMatrix U := rfl

/-- The action matrix of the species is the action matrix of the datum. -/
example (c : GaugeAlgebra) : leptonDoublet.rep.act c = LeptonDoublet.actionMatrix c := rfl

/-- The target space of the species is the target space of the datum. -/
example : LeptonDoublet = leptonDoublet.V := rfl

/-- **The matter field of the datum is the matter field of the species**: the table's
  description and the species' description of the lepton doublet are one definition. -/
lemma leptonDoublet_toMatterField_eq :
    leptonDoublet.toMatterField = LeptonDoublet.matterField := rfl

end Model

end StandardModel
