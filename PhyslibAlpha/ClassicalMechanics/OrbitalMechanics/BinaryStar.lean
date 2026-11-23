/-
Copyright (c) 2026 Qianli Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qianli Ma
-/
module

public import Physlib.ClassicalMechanics.PointParticle.NewtonianSystem.CenterOfMass
public import PhyslibAlpha.ClassicalMechanics.OrbitalMechanics.NewtonianGravity
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic.Module

/-!
# The Newtonian two-body reduction
The center of mass and relative displacement of two stars in an inertial frame.

## i. Overview

An equivalence with `Fin 2` labels the two particle occurrences. Their center of mass moves
uniformly in the absence of external forces. Together with the relative displacement, the center
of mass determines both positions. If their internal forces are the pairwise Newtonian
forces, the relative displacement from star zero to star one satisfies the Kepler equation at
each time of positive separation. The gravitational parameter is `G` times the sum of the masses.
For positive `G` the relative acceleration points towards zero displacement.

## ii. Key results

- `centerOfMass_eq_of_two_particles` gives the mass-weighted position of the binary.
- `positions_eq_centerOfMass_relativePosition` recovers both positions from the center of mass
  and the displacement from the first particle to the second.
- `hasDerivAt_deriv_relativePosition_of_gravity` gives the relative acceleration.

## iii. Table of contents

- A. The center of mass of a binary
- B. Relative motion under gravity

## iv. References

* [ref: goldstein_classicalmechanics], Chapter 3.
-/

@[expose] public noncomputable section

open scoped BigOperators Classical

namespace ClassicalMechanics.PointParticle.NewtonianSystem

open ReferenceFrame

variable {d : ℕ} (system : NewtonianSystem d) (e : Fin 2 ≃ system.Particle)

/-!
## A. The center of mass of a binary
-/

/-- The center of mass of two labelled particles, in the system's frame coordinates. -/
lemma centerOfMass_eq_of_two_particles (t : ℝ) :
    system.centerOfMass t = ((e 0).mass.val + (e 1).mass.val)⁻¹ •
      ((e 0).mass.val • (e 0).pos t + (e 1).mass.val • (e 1).pos t) := by
  change (∑ p : system.Particle, p.mass.val)⁻¹ • (∑ p : system.Particle, p.mass.val • p.pos t) = _
  rw [← e.sum_comp (fun p => p.mass.val), ← e.sum_comp (fun p => p.mass.val • p.pos t)]
  simp only [Fin.sum_univ_two]

/-- The two positions are recovered from their center of mass and relative displacement.
Each offset from the center of mass is weighted by the other particle's mass. -/
lemma positions_eq_centerOfMass_relativePosition (t : ℝ) :
    let r := (e 1).pos t - (e 0).pos t
    let M := (e 0).mass.val + (e 1).mass.val
    (e 0).pos t = system.centerOfMass t - ((e 1).mass.val / M) • r ∧
      (e 1).pos t = system.centerOfMass t + ((e 0).mass.val / M) • r := by
  dsimp only
  rw [system.centerOfMass_eq_of_two_particles e t]
  have hM := ne_of_gt (add_pos (e 0).mass.property (e 1).mass.property)
  constructor <;> match_scalars <;> field_simp [hM] <;> ring

/-!
## B. Relative motion under gravity
-/

variable (G : ℝ)

private lemma acceleration_eq_pairGravityAcceleration
    (hi : system.internalForces = gravityForces G system.particles)
    (he : system.externalForces = 0) (i j : Fin 2) (hij : j ≠ i) (t : ℝ) :
    (e i).acceleration t = pairGravityAcceleration G system.particles (e j) (e i) t := by
  have ha : (e i).acceleration t = gravityAcceleration G system.particles (e i) t :=
    (acceleration_eq_gravity_iff G system.particles (e i) t).mpr (by
      rw [← hi, ← he]
      exact congrFun (system.newton_second_law (e i)) t)
  rw [ha, gravityAcceleration]
  let source : {p : system.Particle // p ≠ e i} := ⟨e j, e.injective.ne hij⟩
  have only_source (p : {p : system.Particle // p ≠ e i}) : p = source := by
    obtain ⟨k, hk⟩ := e.surjective p.val
    have hki : k ≠ i := fun h => p.property (hk.symm.trans (congrArg e h))
    have hkj : k = j := by omega
    exact Subtype.ext (hk.symm.trans (congrArg e hkj))
  exact Finset.sum_eq_single_of_mem source (Finset.mem_univ _) fun b _ h =>
    (h (only_source b)).elim

/-- At a collision-free time the relative displacement of two mutually gravitating particles
satisfies the Kepler equation with gravitational parameter `G` times their total mass. -/
lemma hasDerivAt_deriv_relativePosition_of_gravity
    (hi : system.internalForces = gravityForces G system.particles)
    (he : system.externalForces = 0) {t : ℝ} (hne : (e 1).pos t ≠ (e 0).pos t) :
    let r := fun s => (e 1).pos s - (e 0).pos s
    HasDerivAt (deriv r)
      (-(G * ((e 0).mass.val + (e 1).mass.val) / ‖r t‖ ^ 3) • r t) t := by
  let r := fun s => (e 1).pos s - (e 0).pos s
  change HasDerivAt (deriv r) _ t
  have hp (i : Fin 2) (s : ℝ) : HasDerivAt (e i).pos ((e i).velocity s) s :=
    ((e i).1.pos_twice_differentiable system.isInertial.out).1 s |>.hasDerivAt
  have hv (i : Fin 2) : HasDerivAt (e i).velocity ((e i).acceleration t) t :=
    ((e i).1.pos_twice_differentiable system.isInertial.out).2 t |>.hasDerivAt
  have hr : deriv r = fun s => (e 1).velocity s - (e 0).velocity s :=
    funext fun s => ((hp 1 s).sub (hp 0 s)).deriv
  rw [hr]
  convert (hv 1).sub (hv 0) using 1
  rw [acceleration_eq_pairGravityAcceleration system e G hi he 1 0 (by decide) t,
    acceleration_eq_pairGravityAcceleration system e G hi he 0 1 (by decide) t]
  change -(G * ((e 0).mass.val + (e 1).mass.val) / ‖r t‖ ^ 3) • r t =
    (G * (e 0).mass.val / ‖(e 0).pos t - (e 1).pos t‖ ^ 3) • ((e 0).pos t - (e 1).pos t) -
    (G * (e 1).mass.val / ‖r t‖ ^ 3) • r t
  rw [show (e 0).pos t - (e 1).pos t = -r t by simp [r], norm_neg, smul_neg, ← neg_smul,
    ← sub_smul]
  congr 1
  have hrpos : ‖r t‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne)
  field_simp [hrpos]
  ring

end ClassicalMechanics.PointParticle.NewtonianSystem
