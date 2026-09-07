/-
Copyright (c) 2026 Nathaneal Sajan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaneal Sajan
-/
module

public import Physlib.Particles.StandardModel.Fermions.LeptonSinglet.JetComponentSpace
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
/-!
# The jet algebra of the charged-lepton singlet

## i. Overview

The jet algebra of the charged-lepton singlet is the exterior algebra on its jet
component space. It is the algebra in which the charged-lepton part of a
Lagrangian lives: the generators are the component functions `∂_s ψ_α` and their
conjugates, and the exterior product implements the anticommutativity of
fermionic fields.

## ii. Key results

- `JetAlgebra` : the exterior algebra on the jet component space.
- `JetAlgebra.ofGenerator` : the jet-algebra element of a generator.

## iii. Table of contents

- A. The jet algebra
  - A.1. The generators of the jet algebra

-/

@[expose] public section

namespace StandardModel

namespace LeptonSinglet

open TensorProduct LagrangianTheory

/-!

## A. The jet algebra

-/


abbrev JetAlgebra : Type := ExteriorAlgebra ℂ JetComponentSpace

namespace JetAlgebra


/-!

### A.1. The generators of the jet algebra

-/

noncomputable def ofGenerator (j : JetGenerators) : JetAlgebra :=
  ExteriorAlgebra.ι ℂ (JetComponentSpace.basis j)

end JetAlgebra

end LeptonSinglet

end StandardModel
