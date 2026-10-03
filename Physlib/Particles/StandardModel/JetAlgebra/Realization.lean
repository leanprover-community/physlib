/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module
public import Physlib.Particles.StandardModel.AlgebraRealization.Basic
/-!
# The jet algebra of the Standard Model is a Standard Model

## i. Overview

`AlgebraRealization` asks an algebra for an equivariant algebra map out of the jet algebra
of the Standard Model. The jet algebra therefore carries one for free — the identity — and
that is all this file records. The four compatibility laws hold by definition, and the two
multiplicativity laws are the ones the jet gauge action and the Lorentz action were shown
to satisfy when they were built.

It is the point at which the abstract theory of `AlgebraRealization` — its covariant
reduction, its mass-weight filtration and its classification of invariants — becomes a
theory of the concrete algebra in which a Standard Model Lagrangian is written, and it is
the first file on the concrete side of that divide. What the instance then buys, once the
covariant reduction is available, is [`CovJetAlgebra/Basic.lean`](CovJetAlgebra/Basic.lean);
what it buys for the classification is
[`AlgebraRealization.lean`](AlgebraRealization.lean).

## ii. Key results

- `StandardModel.AlgebraRealization.id` : the jet algebra of the Standard Model is a
  Standard Model, along the identity algebra map.

## iii. Table of contents

- A. The identity realization

-/

@[expose] public section

namespace StandardModel

namespace AlgebraRealization

open TensorProduct Matrix MatrixGroups Lorentz

/-!

## A. The identity realization

-/

/-- The jet algebra of the Standard Model is a Standard Model: it is one along the identity
  algebra map. -/
noncomputable def id : AlgebraRealization JetAlgebra JetAlgebra.repJetGaugeGroupI
    JetAlgebra.repLorentzGroup JetAlgebra.massWeightPoly where
  toAlgHom := AlgHom.id ℂ JetAlgebra
  map_repJet _ _ := rfl
  map_repLorentz _ _ := rfl
  map_massWeight x := by
    simp [Polynomial.mapAlgHom]
  repJet_mul := JetAlgebra.repJetGaugeGroupI_apply_mul
  repLorentz_mul := JetAlgebra.repLorentzGroup_apply_mul

end AlgebraRealization

end StandardModel
