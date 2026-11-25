/-
Copyright (c) 2026 Raunak Chhatwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raunak Chhatwal
-/
module

public import Physlib.SpaceAndTime.ReferenceFrame
/-!
# Point particles

This module defines point particles together with their motion relative to a
reference frame. A `Particle` has a constant positive mass and a position over
time. Velocity and acceleration are derived from that position rather than stored
as independent data.

The trajectory is part of the particle's description, but need not be given by an
explicit solution formula. Particle values can be considered subject to conditions
on their positions and on the forces acting on them. A particular mechanical model
can therefore be specified by constraints on particles, with the existence of
particles satisfying those constraints established separately.

A particle by itself carries no equation of motion or assumption about which
forces act on it. It is a constituent from which systems can be assembled, rather
than a specification of an isolated or unconstrained one-particle system. Newton's
laws are imposed when particles and forces are assembled in
`ClassicalMechanics.PointParticle.NewtonianSystem`.

-/

@[expose] public noncomputable section

open scoped BigOperators Classical

namespace ClassicalMechanics.ReferenceFrame

variable {d : ℕ} {frame : ReferenceFrame d}

/-- Positive real numbers. -/
notation "ℝ+" => {x : ℝ // 0 < x}

/-- A point particle in `frame`. -/
structure Particle (frame : ReferenceFrame d) where
  /-- The particle's mass. -/
  mass : ℝ+
  /-- The particle's position in frame coordinates. -/
  pos : ℝ → frame.Vector
  pos_twice_differentiable : Differentiable ℝ pos ∧ Differentiable ℝ (deriv pos)

namespace Particle

variable (particle : frame.Particle)

/-- The particle's velocity. -/
def velocity : ℝ → frame.Vector :=
  deriv particle.pos

/-- The particle's acceleration. -/
def acceleration  : ℝ → frame.Vector :=
  deriv particle.velocity

/-- The particle's position in affine space at frame time coordinate `t`. -/
def pointInSpace (t : ℝ) : Space d :=
  Vector.dispEquiv t (particle.pos t) +ᵥ frame.origin (frame.timeEquiv t)

end ClassicalMechanics.ReferenceFrame.Particle
