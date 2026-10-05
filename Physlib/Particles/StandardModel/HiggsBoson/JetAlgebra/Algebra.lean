/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.HiggsBoson.MatterField
public import Physlib.Particles.StandardModel.Matter.BosonicAlgebra.JetDeriv
public import Physlib.Particles.StandardModel.Matter.BosonicAlgebra.LorentzAction
public import Physlib.Particles.StandardModel.Matter.BosonicAlgebra.GaugeAction
public import Physlib.Particles.StandardModel.Matter.BosonicAlgebra.MassDim
/-!
# The jet algebra of the Higgs field

## i. Overview

The jet algebra of the Higgs field is the bosonic algebra of the Higgs matter field: the
symmetric algebra on its component functions `∂_s H_α` and `∂_s H̄_α`, which commute
because the Higgs is a boson. This file carries the algebra and the actions on it — the
Lorentz action, the jet and global gauge actions, and the mass-dimension scaling — each
obtained by applying the generic bosonic-algebra construction to `HiggsVec.matterField`.

The file is separate from
`Physlib.Particles.StandardModel.HiggsBoson.JetAlgebra.Basic`, which builds the gauge
action on the *jets* of the field, because the matter field is assembled from that action
and the algebra is then built on the matter field: the three steps are a chain, not a
single file.

## ii. Key results

- `StandardModel.HiggsJetAlgebra` : the bosonic algebra of the Higgs matter field.
- `StandardModel.HiggsJetAlgebra.repLorentzGroup`,
  `StandardModel.HiggsJetAlgebra.repJetGaugeGroupI`,
  `StandardModel.HiggsJetAlgebra.repGaugeGroupI` : the actions on it.
- `StandardModel.HiggsJetAlgebra.massWeightScale` : the mass-dimension scaling.

## iii. Table of contents

- B. The jet algebra of the Higgs field
  - B.1. The component functions
  - B.2. The Lorentz action
  - B.3. The jet gauge action
  - B.4. The mass-dimension scaling

-/

@[expose] public section

namespace StandardModel

/-!

## B. The jet algebra of the Higgs field

-/

/-- **The jet algebra of the Higgs field**: the bosonic algebra of the `HiggsVec`-valued
  Higgs field. Its generators are the component functions `∂_s H_α` and `∂_s H̄_α`, and
  they commute — the Higgs is a boson. -/
abbrev HiggsJetAlgebra : Type := BosonicAlgebra HiggsVec.matterField

TODO (lines := 56-62) (date := 2026-09-11) "We should no longer
  need this result, we should just be able to use the general results
  from gauge Theory."

namespace HiggsJetAlgebra

/-!

### B.1. The component functions

-/

/-- The component functions of the Higgs field inside its jet algebra. -/
noncomputable def ofHiggs : Module.Dual ℂ HiggsVec →ₗ[ℂ] HiggsJetAlgebra :=
  BosonicAlgebra.ofField (M := HiggsVec.matterField)

/-- The conjugate component functions of the Higgs field inside its jet algebra. -/
noncomputable def ofConjHiggs :
    Module.Dual ℂ (ConjModule HiggsVec) →ₗ[ℂ] HiggsJetAlgebra :=
  BosonicAlgebra.ofConjField (M := HiggsVec.matterField)

/-!

### B.2. The Lorentz action

-/

open Matrix MatrixGroups in
/-- The Lorentz action on the jet algebra of the Higgs field: the Higgs is a Lorentz
  scalar, so the Lorentz group acts on the component functions only through their
  derivative labels. -/
noncomputable def repLorentzGroup : Representation ℂ SL(2,ℂ) HiggsJetAlgebra :=
  BosonicAlgebra.repLorentzGroup HiggsVec.matterField

/-!

### B.3. The jet gauge action

-/

/-- The jet gauge action on the jet algebra of the Higgs field, lifted from the fibrewise
  action on its jets. -/
noncomputable def repJetGaugeGroupI : Representation ℂ JetGaugeGroupI HiggsJetAlgebra :=
  BosonicAlgebra.repJetGaugeGroupI HiggsVec.matterField

/-- The action of the constant — global — gauge transformations on the jet algebra of the
  Higgs field. -/
noncomputable def repGaugeGroupI : Representation ℂ GaugeGroupI HiggsJetAlgebra :=
  BosonicAlgebra.repGaugeGroupI HiggsVec.matterField

/-!

### B.4. The mass-dimension scaling

-/

/-- The mass-dimension scaling on the jet algebra of the Higgs field: the Higgs has mass
  dimension one, that is mass weight two, and each derivative adds mass weight two. -/
noncomputable def massWeightScale (c : ℂ) : HiggsJetAlgebra →ₐ[ℂ] HiggsJetAlgebra :=
  BosonicAlgebra.massWeightScale (M := HiggsVec.matterField) 2 c

/-- The Higgs field carries mass weight two — mass dimension one. -/
@[simp]
lemma massWeightScale_ofHiggs (c : ℂ) (φ : Module.Dual ℂ HiggsVec) :
    massWeightScale c (ofHiggs φ) = c ^ 2 • ofHiggs φ :=
  BosonicAlgebra.massWeightScale_ofField (M := HiggsVec.matterField) 2 c φ

/-- A derivative of the Higgs field adds mass weight two. -/
lemma massWeightScale_jetDeriv (c : ℂ) (μ : Fin 1 ⊕ Fin 3) (x : HiggsJetAlgebra) :
    massWeightScale c (BosonicAlgebra.jetDeriv μ x)
      = c ^ 2 • BosonicAlgebra.jetDeriv μ (massWeightScale c x) :=
  BosonicAlgebra.massWeightScale_jetDeriv 2 c μ x

end HiggsJetAlgebra

end StandardModel
