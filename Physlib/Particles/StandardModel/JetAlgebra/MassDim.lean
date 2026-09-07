/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.JetAlgebra.Basic
public import Physlib.Particles.StandardModel.GaugeBosons.GaugeJetAlgebra.MassDim
/-!
# The mass-dimension scaling on the jet algebra of the Standard Model

## i. Overview

The mass-dimension scaling on the jet algebra of the Standard Model acts sector by
sector: fermions carry mass weight three, the Higgs weight two, the gauge fields weight
two, and every derivative weight two. A monomial of total mass weight `w` is scaled by
`r ^ w`; the terms of a Lagrangian of mass dimension four are exactly those scaling with
`r ^ 8`.

## ii. Key results

- `JetAlgebra.complexGaugeMassWeightScale` : the scaling on the complexified gauge
  sector.
- `JetAlgebra.massWeightScale` : the mass-dimension scaling on the jet algebra.

## iii. Table of contents

- A. The mass-dimension scaling

-/

@[expose] public section

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 1000000
set_option synthInstance.maxSize 2048
set_option maxRecDepth 8000

namespace StandardModel

open TensorProduct

namespace JetAlgebra

/-!

## A. The mass-dimension scaling

-/

/-- The mass-dimension scaling on the complexified gauge sector. -/
noncomputable def complexGaugeMassWeightScale (r : ℝ) :
    (ℂ ⊗[ℝ] GaugeJetAlgebra) →ₐ[ℂ] (ℂ ⊗[ℝ] GaugeJetAlgebra) :=
  Algebra.TensorProduct.map (AlgHom.id ℂ ℂ) (GaugeJetAlgebra.massWeightScale r)

/-- **The mass-dimension scaling on the jet algebra of the Standard Model**: each sector
  scales by its own mass weights — fermions carry weight three, the Higgs weight two, the
  gauge fields weight two, and every derivative weight two. -/
noncomputable def massWeightScale (r : ℝ) : JetAlgebra →ₐ[ℂ] JetAlgebra :=
  Algebra.TensorProduct.map
    (Algebra.TensorProduct.map (FermionJetAlgebra.massWeightScale (r : ℂ))
      (HiggsJetAlgebra.massWeightScale (r : ℂ)))
    (complexGaugeMassWeightScale r)

end JetAlgebra

end StandardModel
