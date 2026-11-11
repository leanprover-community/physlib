/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaneal Sajan, Joseph Tooby-Smith, Lode Vermeulen
-/
module

public import Physlib.ClassicalMechanics.HarmonicOscillator.Solution.Basic

/-!

# The energy of the trajectories

## i. Overview

Show that the energy is a conserved quantity, i.e. a constant of motion.

## ii. Key results

- `trajectory_energy`: The energy is conserved along any trajectory.

## iii. Table of contents
- A. Conservation of energy

## iv. References

References for the classical harmonic oscillator include:

* Landau & Lifshitz, Mechanics, page 58, section 21. [ref: landau_mechanics]
-/

@[expose] public

noncomputable section

open Real Time ContDiff

variable (S : HarmonicOscillator)

namespace ClassicalMechanics.HarmonicOscillator

/-!

## A. Conservation of energy

For a given set of initial conditions, the energy of the trajectory is constant,
due to the conservation of energy. Here we show it's value.

-/
lemma trajectory_energy (IC : InitialConditions) : S.energy (IC.trajectory S) =
    fun _ => 1/2 * (S.m * ‖IC.v₀‖ ^2 + S.k * ‖IC.x₀‖ ^ 2) := by
  funext t
  rw [energy_conservation_of_equationOfMotion' _ _ (by fun_prop)
    (InitialConditions.trajectory_equationOfMotion S IC)]
  simp [energy, kineticEnergy, potentialEnergy]
  ring_nf

end HarmonicOscillator

end ClassicalMechanics
