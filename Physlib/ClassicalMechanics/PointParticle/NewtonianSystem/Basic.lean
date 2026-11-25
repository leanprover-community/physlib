/-
Copyright (c) 2026 Raunak Chhatwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raunak Chhatwal
-/
module

public import Physlib.ClassicalMechanics.Force
public import Physlib.ClassicalMechanics.PointParticle.Basic
/-!
# Newtonian point-particle systems

This module defines `NewtonianSystem`, consisting of an inertial reference frame, a finite
collection of point particles, and the internal and external forces acting on
them. Particles carry masses and positions over time; forces carry vector values
over time and identify the particles they act on.

Newton's second law requires the net force on each particle to equal its mass
times its acceleration. Newton's third law requires the multiset of internal
forces to be invariant under equal-and-opposite reversal.

Particles and forces are stored in multisets. For example, if two identical springs
connect the same pair of particles, the net force on either particle must count
both spring forces, even though they are equal.

Many classical systems are specified by constraints rather than explicit position
and force functions. Such models can be formalized as conditions on `NewtonianSystem`
values: which particles and forces are present, geometric constraints such as
fixed distances, and restrictions on the forces such as centrality.

Results can be proved for arbitrary systems satisfying these conditions. An
existence proof establishes that a satisfying system exists for given parameters
and initial conditions; choice can then be used to select one. Explicit formulas
for the positions and forces are not required to state the conditions or to
reason about systems satisfying them.
-/

@[expose] public noncomputable section

open scoped BigOperators Classical

namespace ClassicalMechanics.PointParticle

open ReferenceFrame

variable {d : ℕ}

/-!
## A. Systems
-/

/-- A finite system of point particles satisfying Newton's laws. -/
structure NewtonianSystem (d : ℕ) where
  /-- The system's reference frame. -/
  frame : ReferenceFrame d
  frame_inertial : frame.IsInertial
  /-- The particles in the system. -/
  particles : Multiset frame.Particle
  /-- Forces between particles in the system. -/
  internalForces : Multiset (frame.InternalForce particles)
  /-- Forces on the system from external sources. -/
  externalForces : Multiset (frame.Force particles)
  /-- Newton's second law: the net force on each particle equals its mass times its acceleration. -/
  newton_second_law : ∀ particle : particles,
    netForce particle internalForces externalForces = particle.1.mass • particle.1.acceleration
  /-- Newton's third law: internal forces and their reverses occur with equal multiplicities. -/
  newton_third_law : internalForces.map .reverse = internalForces

namespace NewtonianSystem

variable (system : NewtonianSystem d)

/-!
## B. System particles
-/

/-- Vectors in the system's frame. -/
abbrev Vector := system.frame.Vector

/-- A particle in `system`. -/
abbrev Particle : Type := system.particles

namespace Particle

variable {system : NewtonianSystem d} (particle : system.Particle) (t : ℝ)

/-- The particle's mass. -/
def mass : ℝ+ := particle.1.mass

/-- The particle's position at `t`. -/
def pos : system.Vector := particle.1.pos t

/-- The particle's velocity at `t`. -/
def velocity : system.Vector := particle.1.velocity t

/-- The particle's acceleration at `t`. -/
def acceleration : system.Vector := particle.1.acceleration t

/-- The particle's momentum at `t`. -/
def momentum : system.Vector := particle.mass • particle.velocity t

/-- The particle's kinetic energy at `t`. -/
def kineticEnergy : ℝ := particle.mass * ‖particle.velocity t‖ ^ 2 / 2

end Particle

/-!
## C. System forces
-/

/-- A force in `system`. -/
abbrev Force : Type :=
  system.internalForces ⊕ system.externalForces

namespace Force

variable {system : NewtonianSystem d} (force : system.Force)

/-- The underlying force. -/
@[coe] def inner : system.frame.Force system.Particle :=
  match force with | .inl force => force | .inr force => force

instance : Coe system.Force (system.frame.Force system.Particle) := Coe.mk inner

/-- The force at `t`. -/
def value (t : ℝ) : system.Vector := force.inner.value t

instance : CoeFun system.Force (fun _ => ℝ → system.Vector) where
  coe := value

/-- The force's target. -/
def target : system.Particle := force.inner.target

/-- Whether `force` is internal. -/
def Internal : Prop := force.isLeft

/-- Whether `force` is external. -/
def External : Prop := force.isRight

end Force

/-- An internal force in `system`. -/
abbrev InternalForce : Type := system.internalForces

namespace InternalForce

variable {system : NewtonianSystem d} (force : system.InternalForce)

/-- View an internal force as a system force. -/
instance : Coe system.InternalForce system.Force := Coe.mk .inl

/-- The force at `t`. -/
def value (t : ℝ) : system.Vector := force.1.value t

/-- The force's target. -/
def target : system.Particle := force.1.target

/-- The force's source. -/
def source : system.Particle := force.1.source

/-- A force and its reverse have the same multiplicity. -/
lemma reverse_count_eq :
    system.internalForces.count force.1.reverse = system.internalForces.count force.1 := by
  rw [← congrArg (Multiset.count force.1.reverse) system.newton_third_law]
  refine Multiset.count_map_eq_count' _ _ (Function.Involutive.injective ?_) _
  intro internalForce
  rcases internalForce with ⟨⟨value, target⟩, source, source_ne_target⟩
  simp [ReferenceFrame.InternalForce.reverse]

/-- The reverse force. -/
def reverse : system.InternalForce :=
  ⟨force.1.reverse, (finCongr force.reverse_count_eq).symm force.2⟩

/-- Whether the force lies along the line joining its source and target. -/
def Central : Prop :=
  ∀ t, ∃ c : ℝ, force.value t = c • (force.target.pos t - force.source.pos t)

end InternalForce

/-- The internal forces cancel in pairs by Newton's third law. -/
lemma internalForce_sum_zero (t : ℝ) :
    (system.internalForces.map (fun f => f.value t)).sum = 0 := by
  let value := fun f : system.frame.InternalForce system.Particle => f.value t
  have h : (system.internalForces.map value).sum = -(system.internalForces.map value).sum := calc
    _ = ((system.internalForces.map .reverse).map value).sum :=
      congrArg (fun fs => (fs.map value).sum) system.newton_third_law.symm
    _ = _ := by
      rw [Multiset.map_map, ← Multiset.sum_map_neg]
      rfl
  apply smul_right_injective system.Vector (by norm_num : (2 : ℝ) ≠ 0)
  change (2 : ℝ) • (system.internalForces.map value).sum = (2 : ℝ) • (0 : system.Vector)
  rw [smul_zero, two_smul, ← eq_neg_iff_add_eq_zero]
  exact h

/-- With no external forces, the sum of mass times acceleration vanishes. -/
lemma sum_mass_acceleration_eq_zero (hExt : system.externalForces = 0) (t : ℝ) :
    ∑ p : system.Particle, p.mass.val • p.acceleration t = 0 := by
  classical
  simp_rw [show ∀ p : system.Particle, p.mass.val • p.acceleration t =
      netForce p system.internalForces system.externalForces t from
    fun p => (congrFun (system.newton_second_law p) t).symm]
  simp only [netForce, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  let forces := system.internalForces.map InternalForce.toForce + system.externalForces
  let value := fun f : system.frame.Force system.Particle => f.value t
  change ((Finset.univ : Finset forces).val.map (fun f => value f.1)).sum = 0
  rw [Multiset.map_univ forces value]
  simpa only [forces, hExt, add_zero, Multiset.map_map, value, Function.comp_def] using
    system.internalForce_sum_zero t

/-!
## D. Aggregate quantities
-/

variable (t : ℝ)

/-- Total mass. -/
def mass : ℝ :=
  ∑ particle : system.Particle, particle.mass

/-- Total momentum at `t`. -/
def momentum : system.Vector :=
  ∑ particle : system.Particle, particle.momentum t

/-- Net external force at `t`. -/
def netExternalForce : system.Vector :=
  ∑ force : system.Force with force.External, force t

/-- Total kinetic energy at `t`. -/
def kineticEnergy : ℝ :=
  ∑ particle : system.Particle, particle.kineticEnergy t

end ClassicalMechanics.PointParticle.NewtonianSystem
