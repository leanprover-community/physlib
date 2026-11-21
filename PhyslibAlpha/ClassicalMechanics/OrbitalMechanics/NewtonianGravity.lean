/-
Copyright (c) 2026 Qianli Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qianli Ma
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Data.Finset.BooleanAlgebra
public import Physlib.ClassicalMechanics.PointParticle.NewtonianSystem.Basic
import Mathlib.Tactic.Ring

/-!
# Pairwise Newtonian gravitation
Pair forces for a finite collection of point particles in a reference frame.

## i. Overview

For a source of mass `m`, the gravitational acceleration of a target is proportional to
`G * m` times the displacement towards the source divided by the cube of the separation.
Here `G` is the gravitational constant in the frame's units. The force multiplies the
acceleration by the target mass. Each ordered pair of distinct particle occurrences supplies
one internal force, preserving multiplicities in the particle multiset.

The formulas use the frame's physical norm. They model Newtonian gravity at collision-free
times. At coincidence the Lean expression has value zero by totalized division.

## ii. Key results

- `ReferenceFrame.gravityForces_reverse` proves Newton's third law for the force multiset.
- `ReferenceFrame.netForce_gravity` expresses the net force as mass times acceleration.
- `PointParticle.NewtonianSystem.ofGravity` bundles a solution of the acceleration equations
  as a Newtonian system in an inertial frame.

## iii. Table of contents

- A. Gravitational forces and acceleration
- B. Newtonian systems under gravity

## iv. References

* [ref: goldstein_classicalmechanics], Chapter 3, for the inverse-square gravitational force.
-/

@[expose] public noncomputable section

open scoped BigOperators Classical

namespace ClassicalMechanics.ReferenceFrame

/-!
## A. Gravitational forces and acceleration
-/

variable {d : ℕ} {frame : ReferenceFrame d} [Fact frame.IsMetricConserved]
variable (G : ℝ) (particles : Multiset frame.Particle)

/-- The contribution of the source to the target's gravitational acceleration. -/
def pairGravityAcceleration (source target : particles) (t : ℝ) : frame.Vector :=
  let displacement := source.1.pos t - target.1.pos t
  (G * source.1.mass.val / ‖displacement‖ ^ 3) • displacement

/-- The target's gravitational acceleration from all other particle occurrences. -/
def gravityAcceleration (target : particles) (t : ℝ) : frame.Vector :=
  ∑ source : {source : particles // source ≠ target},
    pairGravityAcceleration G particles source target t

/-- The Newtonian force exerted by one particle on another in the given frame. -/
def pairGravity (source target : particles) (hne : source ≠ target) :
    frame.InternalForce particles where
  source := source
  target := target
  source_ne_target := hne
  value t := target.1.mass • pairGravityAcceleration G particles source target t

/-- Exchanging source and target gives the equal and opposite force. -/
lemma pairGravity_reverse (source target : particles) (hne : source ≠ target) :
    (pairGravity G particles source target hne).reverse =
      pairGravity G particles target source hne.symm := by
  have hvalue : -(pairGravity G particles source target hne).value =
      (pairGravity G particles target source hne.symm).value := by
    funext t
    let displacement := source.1.pos t - target.1.pos t
    change -(target.1.mass.val • ((G * source.1.mass.val / ‖displacement‖ ^ 3) • displacement)) =
      source.1.mass.val • ((G * target.1.mass.val /
        ‖target.1.pos t - source.1.pos t‖ ^ 3) • (target.1.pos t - source.1.pos t))
    rw [norm_sub_rev (target.1.pos t) (source.1.pos t), ← neg_sub (source.1.pos t),
      smul_smul, smul_smul, smul_neg]
    congr 2
    ring
  change InternalForce.mk (Force.mk _ source) target hne.symm =
    InternalForce.mk (Force.mk _ source) target hne.symm
  exact congrArg (fun value => InternalForce.mk (Force.mk value source) target hne.symm) hvalue

/-- All ordered pairs of distinct particle occurrences, grouped by target. -/
abbrev GravityPairs := Σ target : particles, {source : particles // source ≠ target}

/-- The internal gravitational forces, with each ordered pair occurring once. -/
def gravityForces : Multiset (frame.InternalForce particles) :=
  (Finset.univ : Finset (GravityPairs particles)).val.map fun pair =>
    pairGravity G particles pair.2.1 pair.1 pair.2.2

/-- Newton's third law for the collection of pairwise gravitational forces. -/
lemma gravityForces_reverse :
    (gravityForces G particles).map InternalForce.reverse = gravityForces G particles := by
  let exchange : GravityPairs particles ≃ GravityPairs particles :=
    { toFun := fun p => ⟨p.2.1, ⟨p.1, p.2.2.symm⟩⟩
      invFun := fun p => ⟨p.2.1, ⟨p.1, p.2.2.symm⟩⟩
      left_inv := fun ⟨_, ⟨_, _⟩⟩ => rfl
      right_inv := fun ⟨_, ⟨_, _⟩⟩ => rfl }
  unfold gravityForces
  rw [Multiset.map_map]
  conv_rhs => rw [← Finset.map_univ_equiv exchange]
  rw [Finset.map_val, Multiset.map_map]
  congr 1
  funext pair
  exact pairGravity_reverse G particles pair.2.1 pair.1 pair.2.2

/-- The net internal force is the target mass times its gravitational acceleration. -/
lemma netForce_gravity (target : particles) (t : ℝ) :
    netForce target (gravityForces G particles) 0 t =
      target.1.mass • gravityAcceleration G particles target t := by
  unfold netForce
  rw [add_zero]
  let forces := (gravityForces G particles).map InternalForce.toForce
  let onTarget (force : frame.Force particles) : frame.Vector :=
    if force.target = target then force.value t else 0
  rw [Finset.sum_filter]
  change ((Finset.univ : Finset forces).val.map fun force => onTarget force.1).sum = _
  rw [Multiset.map_univ forces onTarget]
  unfold forces gravityForces
  rw [Multiset.map_map, Multiset.map_map]
  change (∑ pair : GravityPairs particles,
      if pair.1 = target then
        pair.1.1.mass • pairGravityAcceleration G particles pair.2.1 pair.1 t else 0) = _
  rw [Fintype.sum_sigma]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, gravityAcceleration]
  change (∑ source : {source : particles // source ≠ target},
      target.1.mass.val • pairGravityAcceleration G particles source target t) = _
  exact (Finset.smul_sum ..).symm

/-- In an inertial frame, the gravitational acceleration equation is equivalent to Newton's
second law for the constructed internal forces. -/
lemma acceleration_eq_gravity_iff [Fact frame.IsInertial]
    (target : particles) (t : ℝ) :
    target.1.acceleration t = gravityAcceleration G particles target t ↔
      netForce target (gravityForces G particles) 0 t =
        target.1.mass • target.1.acceleration t := by
  rw [netForce_gravity]
  change target.1.acceleration t = gravityAcceleration G particles target t ↔
    target.1.mass.val • gravityAcceleration G particles target t =
      target.1.mass.val • target.1.acceleration t
  rw [(smul_right_injective _ (ne_of_gt target.1.mass.property)).eq_iff, eq_comm]

end ClassicalMechanics.ReferenceFrame

namespace ClassicalMechanics.PointParticle.NewtonianSystem

/-!
## B. Newtonian systems under gravity
-/

open ReferenceFrame

variable {d : ℕ} {frame : ReferenceFrame d} [Fact frame.IsInertial]

/-- Bundle particles that follow the gravitational equations of motion as a Newtonian system
with no external forces. The inverse-square law describes the motion at collision-free times. -/
def ofGravity (G : ℝ) (particles : Multiset frame.Particle)
    (motion : ∀ (target : particles) (t : ℝ),
      target.1.acceleration t = gravityAcceleration G particles target t) :
    NewtonianSystem d where
  frame := frame
  isInertial := inferInstance
  particles := particles
  internalForces := gravityForces G particles
  externalForces := 0
  newton_second_law target := funext fun t =>
    (acceleration_eq_gravity_iff G particles target t).mp (motion target t)
  newton_third_law := gravityForces_reverse G particles

end ClassicalMechanics.PointParticle.NewtonianSystem
