/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.JetAlgebra.Basic
public import Physlib.Particles.StandardModel.Matter.FermionicAlgebra.GaugeAction
public import Physlib.Particles.StandardModel.Matter.BosonicAlgebra.GaugeAction
public import Physlib.Particles.StandardModel.GaugeBosons.GaugeJetAlgebra.GaugeAction
/-!
# The jet gauge action on the jet algebra of the Standard Model

## i. Overview

The jet gauge group acts on the jet algebra of the Standard Model sector by sector: the
tensor product of the fermionic, Higgs and complexified gauge-boson actions. The action is
multiplicative — a jet of gauge transformations acts on a Lagrangian term factor by
factor — and restricts to the gauge sector's own substitution action through the sector
inclusion.

## ii. Key results

- `JetAlgebra.repJetGaugeGroupI` : the jet gauge action.
- `JetAlgebra.repJetGaugeGroupI_apply_mul` : the action is multiplicative.
- `JetAlgebra.repJetGaugeGroupI_includeGauge` : the restriction to the gauge sector.

## iii. Table of contents

- A. The action of the jet gauge group
  - A.1. Multiplicativity
  - A.2. The action on the gauge sector

-/

@[expose] public section

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 1000000
set_option synthInstance.maxSize 2048
set_option maxRecDepth 8000

namespace StandardModel

open TensorProduct Matrix MatrixGroups

namespace JetAlgebra

/-!

## A. The action of the jet gauge group

-/

/-- The jet gauge action on the jet algebra of the Standard Model: the three sectors
  transform independently. -/
noncomputable def repJetGaugeGroupI : Representation ℂ JetGaugeGroupI JetAlgebra :=
  (FermionJetAlgebra.repJetGaugeGroupI.tprod HiggsJetAlgebra.repJetGaugeGroupI).tprod
    GaugeJetAlgebra.complexRepJetGaugeGroupI

@[simp]
lemma repJetGaugeGroupI_tmul (U : JetGaugeGroupI)
    (w : FermionJetAlgebra ⊗[ℂ] HiggsJetAlgebra) (g : ℂ ⊗[ℝ] GaugeJetAlgebra) :
    repJetGaugeGroupI U (w ⊗ₜ[ℂ] g)
      = ((FermionJetAlgebra.repJetGaugeGroupI.tprod
            HiggsJetAlgebra.repJetGaugeGroupI) U w)
          ⊗ₜ[ℂ] (GaugeJetAlgebra.complexRepJetGaugeGroupI U g) := rfl

/-!

### A.1. Multiplicativity

-/

/-- The jet gauge action on the jet algebra is multiplicative: a jet of gauge
  transformations acts on a Lagrangian term factor by factor. -/
lemma repJetGaugeGroupI_apply_mul (U : JetGaugeGroupI) (x y : JetAlgebra) :
    repJetGaugeGroupI U (x * y) = repJetGaugeGroupI U x * repJetGaugeGroupI U y :=
  Representation.tprod_apply_mul _ _
    (Representation.tprod_apply_mul _ _
      (FermionicAlgebra.repJetGaugeGroupI_apply_mul _ _)
      (BosonicAlgebra.repJetGaugeGroupI_apply_mul _ _))
    GaugeJetAlgebra.complexRepJetGaugeGroupI_apply_mul U x y

/-!

### A.2. The action on the gauge sector

-/

/-- The jet gauge action restricts to the gauge sector's own action. -/
lemma repJetGaugeGroupI_includeGauge (U : JetGaugeGroupI)
    (y : ℂ ⊗[ℝ] GaugeJetAlgebra) :
    repJetGaugeGroupI U (includeGauge y)
      = includeGauge (GaugeJetAlgebra.complexRepJetGaugeGroupI U y) := by
  rw [includeGauge_apply, repJetGaugeGroupI_tmul,
    show (FermionJetAlgebra.repJetGaugeGroupI.tprod
        HiggsJetAlgebra.repJetGaugeGroupI) U
        ((1 : FermionJetAlgebra) ⊗ₜ[ℂ] (1 : HiggsJetAlgebra))
      = (FermionJetAlgebra.repJetGaugeGroupI U (1 : FermionJetAlgebra)) ⊗ₜ[ℂ]
        (HiggsJetAlgebra.repJetGaugeGroupI U (1 : HiggsJetAlgebra)) from rfl,
    show HiggsJetAlgebra.repJetGaugeGroupI U (1 : HiggsJetAlgebra) = 1 from
      BosonicAlgebra.repJetGaugeGroupI_apply_one _ _ U,
    show FermionJetAlgebra.repJetGaugeGroupI U (1 : FermionJetAlgebra) = 1 from
      FermionicAlgebra.repJetGaugeGroupI_apply_one _ _ U,
    includeGauge_apply]

end JetAlgebra

end StandardModel
