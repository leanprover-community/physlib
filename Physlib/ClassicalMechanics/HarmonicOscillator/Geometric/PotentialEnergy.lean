/-
Copyright (c) 2026 Robert Forrest. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Forrest
-/
module

public import Physlib.ClassicalMechanics.HarmonicOscillator.Basic
public import Physlib.ClassicalMechanics.HarmonicOscillator.Geometric.Basic
import Physlib.SpaceAndTime.Space.Module

/-!
# Geometric potential energy of the harmonic oscillator

Spring potential energy is determined by the distance from equilibrium.

## i. Overview

At configuration `q`, the oscillator occupies the point `q.toSpace` in physical space
`Space 1`. With equilibrium at the origin, the spring extension has magnitude
`dist q.toSpace 0`. The geometric potential energy is half the spring constant `S.k` times
the square of this distance. It vanishes at equilibrium and takes the same value for equal
displacements on either side. In the global coordinate, the distance is `‖q.val‖`, so the
geometric definition recovers `S.potentialEnergy q.val`.

## ii. Key results

- `geometricPotentialEnergy` assigns the energy `(1 / 2) * S.k * dist q.toSpace 0 ^ 2`
  to a configuration `q`.
- `geometricPotentialEnergy_eq_potentialEnergy` identifies it with the coordinate potential energy.

## iii. Table of contents

- A. Spring potential energy

## iv. References

* See `Physlib.ClassicalMechanics.HarmonicOscillator.Basic` for the coordinate energy.
-/

@[expose] public section

namespace ClassicalMechanics.HarmonicOscillator

/-!
## A. Spring potential energy
-/

/-- The spring potential energy is half the spring constant times the squared distance
from the equilibrium position at the origin. -/
noncomputable def geometricPotentialEnergy (S : HarmonicOscillator) (q : ConfigurationSpace) : ℝ :=
  (1 / 2 : ℝ) * S.k * dist q.toSpace (0 : Space 1) ^ 2

/-- The physical displacement and the global coordinate give the same spring potential energy. -/
lemma geometricPotentialEnergy_eq_potentialEnergy
    (S : HarmonicOscillator) (q : ConfigurationSpace) :
    S.geometricPotentialEnergy q = S.potentialEnergy q.val := by
  have hnorm : ‖q.val‖ = ‖q.toSpace‖ := Space.basis.repr.norm_map q.toSpace
  simp only [geometricPotentialEnergy, potentialEnergy_eq, dist_zero_right, smul_eq_mul,
    real_inner_self_eq_norm_sq, hnorm, mul_assoc]

end ClassicalMechanics.HarmonicOscillator
