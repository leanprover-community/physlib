/-
Copyright (c) 2026 Jinzheng Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li
-/
module

public import Physlib.Particles.StandardModel.Basic
public import Physlib.Particles.StandardModel.GaugeGroup.LocalGaugeData
public import Physlib.Particles.StandardModel.Fermions.QuarkDoublet.GaugeAlgebraAction
/-!
# Consistency of the Standard Model table with the existing formalisation

## i. Overview

The Standard Model of `Physlib.Particles.StandardModel.Basic` is built from its table
alone. This file checks it against the hand-built formalisation: the local gauge data
assembled from the factors is the existing `StandardModel.localGaugeData`, and the quark
row acts by the existing colour–weak matrix of the quark doublet.

## ii. Key results

- `StandardModel.Model.localGaugeData_eq` : the gauge data of the table is the existing
  local gauge data of the Standard Model.
- `StandardModel.Model.quarkDoublet_rep_mat` : the quark doublet reproduces
  `QuarkDoublet.jetGaugeMatrix`, on the same index type.

-/

@[expose] public section

open LocalGaugeData Matrix

namespace StandardModel

namespace Model

/-- The local gauge data assembled from the factors of the table is the existing local
  gauge data of the Standard Model. -/
theorem localGaugeData_eq : StandardModel.localGaugeData = gaugeData := rfl

/-- The quark doublet is indexed by a colour and a weak index, as the existing quark
  doublet. -/
example : quarkDoublet.Idx = (Fin 3 × Fin 2) := rfl

/-- The quark doublet acts on its colour–weak index by the existing matrix `u · (U₃ ⊗ U₂)`
  of the quark doublet. -/
lemma quarkDoublet_rep_mat (U : JetGaugeGroupI) :
    quarkDoublet.rep.mat U = QuarkDoublet.jetGaugeMatrix U := by
  show MatterField.chargePow 1 U.2.2 • Matrix.kroneckerMap (· * ·) U.1.1 U.2.1.1
    = QuarkDoublet.jetGaugeMatrix U
  simp [MatterField.chargePow, QuarkDoublet.jetGaugeMatrix]

end Model

end StandardModel
