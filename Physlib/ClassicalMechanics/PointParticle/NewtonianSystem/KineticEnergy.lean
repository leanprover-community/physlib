/-
Copyright (c) 2026 Qianli Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raunak Chhatwal, Qianli Ma
-/
module

public import Physlib.ClassicalMechanics.PointParticle.NewtonianSystem.CenterOfMass
import Mathlib.Tactic.Ring

/-!
# Kinetic energy of a Newtonian system
The total kinetic energy splits into motion of the center of mass and motion relative to it.

## i. Overview

The total kinetic energy is the sum of the particles' kinetic energies.
The velocity of the center of mass is the mass-weighted average of the particle velocities.
When each particle velocity is written as the sum of this velocity and its relative velocity,
the cross terms in the total kinetic energy cancel.

## ii. Key results

- `Particle.kineticEnergy` and `kineticEnergy` give the particle and system kinetic energies.
- `kineticEnergy_eq_centerOfMass_add_relative` gives the kinetic-energy decomposition.

## iii. Table of contents

- A. Particle and system kinetic energy
- B. Kinetic energy decomposition

## iv. References

* [ref: goldstein_classicalmechanics], Chapter 1.
-/

@[expose] public noncomputable section

open scoped BigOperators Classical InnerProductSpace

namespace ClassicalMechanics.PointParticle.NewtonianSystem

variable {d : ℕ}

/-!
## A. Particle and system kinetic energy
-/

/-- The kinetic energy of a particle at time `t`. -/
def Particle.kineticEnergy {system : NewtonianSystem d} (particle : system.Particle) (t : ℝ) : ℝ :=
  particle.mass * ‖particle.velocity t‖ ^ 2 / 2

/-- The total kinetic energy of a Newtonian system at time `t`. -/
def kineticEnergy (system : NewtonianSystem d) (t : ℝ) : ℝ :=
  ∑ particle : system.Particle, particle.kineticEnergy t

/-!
## B. Kinetic energy decomposition
-/

/-- The total kinetic energy is the sum of the translational kinetic energy of the center
of mass and the kinetic energy of the particles relative to it. -/
lemma kineticEnergy_eq_centerOfMass_add_relative (S : NewtonianSystem d) (t : ℝ) :
    let v := deriv S.centerOfMass t
    S.kineticEnergy t = S.mass * ‖v‖ ^ 2 / 2 +
      ∑ p : S.Particle, p.mass.val * ‖p.velocity t - v‖ ^ 2 / 2 := by
  let v := deriv S.centerOfMass t
  have hmomentum :
      (∑ p : S.Particle, p.mass.val • (p.velocity t - v)) = S.momentum t - S.mass • v := by
    simp_rw [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul]
    rfl
  have hcross : (∑ p : S.Particle, ⟪p.mass.val • (p.velocity t - v), v⟫_ℝ) = 0 := by
    rw [← sum_inner, hmomentum]
    by_cases hmass : S.mass = 0
    · simp [v, (S.hasDerivAt_centerOfMass t).deriv, hmass]
    · simp [v, (S.hasDerivAt_centerOfMass t).deriv, smul_smul, hmass]
  change S.kineticEnergy t = S.mass * ‖v‖ ^ 2 / 2 +
    ∑ p : S.Particle, p.mass.val * ‖p.velocity t - v‖ ^ 2 / 2
  unfold kineticEnergy
  calc
    _ = ∑ p : S.Particle, (p.mass.val * ‖v‖ ^ 2 / 2 +
          p.mass.val * ‖p.velocity t - v‖ ^ 2 / 2 +
          ⟪p.mass.val • (p.velocity t - v), v⟫_ℝ) := by
      apply Finset.sum_congr rfl
      intro p _
      rw [Particle.kineticEnergy, norm_sub_sq_real, real_inner_smul_left, inner_sub_left,
        real_inner_self_eq_norm_sq]
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib, hcross, add_zero, Finset.sum_add_distrib,
        ← Finset.sum_div, ← Finset.sum_mul]
      rfl

end ClassicalMechanics.PointParticle.NewtonianSystem
