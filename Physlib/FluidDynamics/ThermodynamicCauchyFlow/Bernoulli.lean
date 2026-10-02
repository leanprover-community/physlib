/-
Copyright (c) 2026 Florian Wiesner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Wiesner, Michał Mogielnicki
-/
module

public import Physlib.FluidDynamics.FluidFlow.Kinematics
public import Physlib.FluidDynamics.ThermodynamicCauchyFlow.Basic
/-!

# Bernoulli theory for thermodynamic Cauchy flows

## i. Overview

This module is reserved for Bernoulli definitions and results based on the shared
`ThermodynamicCauchyFlow` data together with an explicit external potential parameter, rather
than defining a separate Bernoulli-flow structure.

## ii. Key results

- `bernoulliFunction` : The Bernoulli function `|u|^2 / 2 + h + Phi`.
- `LocalBernoulliLaw` : Vanishing spatial gradient of the Bernoulli function.
- `BernoulliLaw` : Spatial constancy of the Bernoulli function at each time.

## iii. Table of contents

- A. Bernoulli function
- B. Bernoulli-law predicates

## iv. References

* None.
-/

@[expose] public section

open Space

namespace FluidDynamics

/-!

## A. Bernoulli function

-/

/-- The Bernoulli function `|u|^2 / 2 + h + Phi`. -/
noncomputable def bernoulliFunction
    (d : ℕ) (flow : ThermodynamicCauchyFlow d) (potential : Space d → ℝ) : ScalarField d :=
  fun t x => FluidFlow.specificKineticEnergy d flow.toFluidFlow t x + flow.enthalpy t x +
    potential x

/-!

## B. Bernoulli-law predicates

-/

/-- A local Bernoulli law: the Bernoulli function has zero spatial gradient. -/
def LocalBernoulliLaw
    (d : ℕ) (flow : ThermodynamicCauchyFlow d) (potential : Space d → ℝ) : Prop :=
  ∀ t x, (∇ (bernoulliFunction d flow potential t)) x = 0

/-- A global Bernoulli law: the Bernoulli function is spatially constant at each time. -/
def BernoulliLaw
    (d : ℕ) (flow : ThermodynamicCauchyFlow d) (potential : Space d → ℝ) : Prop :=
  ∀ t x y, bernoulliFunction d flow potential t x = bernoulliFunction d flow potential t y

end FluidDynamics
