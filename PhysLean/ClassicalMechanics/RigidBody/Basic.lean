/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.SpaceAndTime.Space.Derivatives.Curl
import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
/-!

# Rigid bodies

A rigid body is one where the distance and relative orientation between particles does not change.
In other words, the body remains undeformed.

In this module we will define the basic properties of a rigid body, including
- mass
- center of mass
- inertia tensor

## References
- Landau and Lifshitz, Mechanics, page 100, Section 32
-/

open Manifold

TODO "MEX5S" "The definition of a rigid body is currently defined via linear maps
  from the space of smooth functions to ℝ. When possible, it should be change
  to *continuous* linear maps. "

/-- A Rigid body defined by its mass distribution. -/
structure RigidBody (d : ℕ) where
  /-- The mass distribution of the rigid body. -/
  ρ : C^⊤⟮𝓘(ℝ, Space d), Space d; 𝓘(ℝ, ℝ), ℝ⟯ →ₗ[ℝ] ℝ

namespace RigidBody

/-- The total mass of the rigid body. -/
def mass {d : ℕ} (R : RigidBody d) : ℝ := R.ρ ⟨fun _ => 1, contMDiff_const⟩

/-- The center of mass of the rigid body. -/
noncomputable def centerOfMass {d : ℕ} (R : RigidBody d) : Space d := ⟨fun i =>
  (1 / R.mass) • R.ρ ⟨fun x => x i, ContDiff.contMDiff <| by fun_prop⟩⟩

/-- The inertia tensor of the rigid body. -/
noncomputable def inertiaTensor {d : ℕ} (R : RigidBody d) :
    Matrix (Fin d) (Fin d) ℝ := fun i j =>
  R.ρ ⟨fun x => (if i = j then 1 else 0) * ∑ k : Fin d, (x k)^2 - x i * x j,
    ContDiff.contMDiff <| by fun_prop⟩

lemma inertiaTensor_symmetric {d : ℕ} (R : RigidBody d) (i j : Fin d) :
    R.inertiaTensor i j = R.inertiaTensor j i := by
  simp only [inertiaTensor]
  congr
  funext x
  congr 1
  · congr 2
    exact Eq.propIntro (fun a => id (Eq.symm a)) fun a => id (Eq.symm a)
  · ring

/-- The kinetic energy of a rigid body. -/
informal_definition kineticEnergy where
  tag := "MEYBM"
  deps := [``RigidBody]

/-- One can describe the motion of rigid body with a fixed (inertial) coordinate system (X,Y,Z)
    and a moving system (x₁,x₂,x₃) rigidly attached to the body. -/
informal_definition coordinate_system where
  tag := "LL31.3"
  deps := [``RigidBody]

/-- A rigid body in three-dimensional space has six degrees of freedom:
    three translational (for the position of its centre of mass) and three
    rotational (for its orientation). -/
informal_lemma rigid_body_dof where
  tag := "LL32-6DF"
  deps := [``RigidBody]

/-- The velocity v of any point in a rigid body is
    v = V + Ω × r,
    where V is the velocity of the origin of the moving system and Ω is the angular velocity. -/
informal_lemma velocity_decomposition where
  tag := "LL31.L3"
  deps := [``RigidBody]

/-- The angular velocity of rotation of a rigid body from a system of coordinates fixed in the
    body is independent of the system chosen. -/
informal_lemma angular_velocity_is_well_defined where
  tag := "LL32-AM"
  deps := [``RigidBody]

/-- The motion of a rigid body can be decomposed into a translation of some reference point plus a
    rotation about that point. There exists a time-dependent vector V(t) and angular velocity ω(t)
    such that v(r) = V + ω × r, where r is measured from the reference point. -/
informal_lemma decomposition_of_motion where
  tag := "LL32-DM"
  deps := [``RigidBody]

/-- The centre of mass of a rigid body moves as if all mass were concentrated at that
    point and acted upon by the resultant external force: M a_CM = ∑ F_ext. -/
informal_lemma center_of_mass_point_moves_as_particle where
  tag := "LL32-CM"
  deps := [``RigidBody]

/-- The total angular momentum about a point O is L = ∫ r × v dm. With v = V + ω × r about the
    centre of mass, L = R × (M V) + I_CM ω, where R is the centre of mass position. -/
informal_lemma angular_momentum_about_point where
  tag := "LL32-L"
  deps := [``RigidBody]

/-- In the inertial frame, the translational equation of motion of a rigid body is given by
    dP/dt = F, where `P` is the total linear momentum and `F` is the total external force acting
    on the body. -/
informal_lemma translational_equation_inertial where
  tag := "LL32-TR"
  deps := [``RigidBody]

/-- In the inertial frame, the rotational equation of motion of a rigid body about the center of
    mass is given by dM/dt = K, where `M` is the total angular momentum and `K` is the total
    external torque. -/
informal_lemma rotational_equation_inertial where
  tag := "LL32-ROT"
  deps := [``RigidBody]

/-- The kinetic energy decomposes into translational and rotational parts:
    T = (1/2) M |V|² + (1/2) ω ⋅ I_CM ω.
    Here V is the velocity of the centre of mass and I_CM is the inertia tensor about that point. -/
informal_lemma kinetic_energy_decomposition where
  tag := "LL32-TK"
  deps := [``RigidBody]

/-- If I_O is the inertia tensor about a point O, then the inertia tensor about a parallel point O'
    displaced by a is I_{O'} = I_O + M(|a|² 1 − a ⊗ a). This is the parallel-axis theorem. -/
informal_lemma parallel_axis_theorem where
  tag := "LL32-PA"
  deps := [``RigidBody]

/-- Because the inertia tensor is real symmetric, there exists an orthonormal basis of principal
    axes in which it is diagonal. The corresponding directions are the principal axes of inertia. -/
informal_definition principal_axes_of_inertia where
  tag := "LL32-PAE"
  deps := [``RigidBody]

/-- None of the principal moments of inertia can exceed the sum of other two. -/
informal_lemma principal_axes_of_inertia_bound where
  tag := "LL32-PAEB"
  deps := [``RigidBody]

/-- An asymmetrical top is when none of the principal moments of inertia are equal. -/
informal_definition asymmetrical_top where
  tag := "LL32-AST"
  deps := [``RigidBody]

/-- A symmetrical top is when only two of the principal moments of inertia are equal. -/
informal_definition symmetrical_top where
  tag := "LL32-ST"
  deps := [``RigidBody]

/-- A spherical top is when all three of the principal moments of inertia are equal. -/
informal_definition spherical_top where
  tag := "LL32-SPT"
  deps := [``RigidBody]

/-- A rotating body-fixed frame is a coordinate system attached to the body
    that rotates with the body relative to an inertial (fixed) frame. The frame
    is characterised by its angular velocity vector Ω(t). -/
informal_definition RotatingFrame where
  tag := "LL32-RF"
  deps := [``RigidBody]

/-- The time derivative in the rotating frame, d'/dt, is the derivative
    of the components of a vector with respect to time when expressed in the
    rotating (body-fixed) frame. -/
informal_definition rotating_frame_derivative where
  tag := "LL32-dprime"
  deps := [``RigidBody]

/-- For any vector field A(t), its inertial-frame time derivative equals the rotating-frame
    derivative plus the contribution from the frame rotation:
      (dA/dt)_inertial = (dA/dt)_rotating + Ω × A.
    Here Ω is the angular velocity of the rotating frame. -/
informal_lemma transport_law_inertial_rotating where
  tag := "LL36-Ltransport"
  deps := [``RigidBody]

/-- For linear momentum, the relation between inertial and rotating derivatives is
      (dP/dt)_inertial = d'P/dt + Ω × P.
    So, d'P/dt + Ω × P = F which is the linear-momentum equation in the rotating frame. -/
informal_lemma transport_law_for_momentum where
  tag := "LL32-transportP"
  deps := [``RigidBody]

/-- For angular momentum, the relation between inertial and rotating derivatives is
      (dM/dt)_inertial = d'M/dt + Ω × M,
    and with the rotational form of Newton's law M_tot = (dM/dt)_inertial this yields
      d'M/dt + Ω × M = K,
    the angular-momentum equation in the rotating frame. -/
informal_lemma transport_law_for_angular_momentum where
  tag := "LL32-transportM"
  deps := [``RigidBody]

/-- When motion is described in body-fixed principal axes (I₁, I₂, I₃ diagonal), the equations of
    rotational motion (Euler’s equations) are:
    I₁ dω₁/dt + (I₃ − I₂) ω₂ ω₃ = M₁, with cyclic permutations.
    M is the external torque about the centre of mass. -/
informal_lemma euler_equations where
  tag := "LL32-EQ"
  deps := [``RigidBody]

/-- A rigid body can perform steady (uniform) rotation about any principal axis if the torque about
    that axis vanishes. Stability depends on the ordering of principal moments. -/
informal_lemma steady_rotation_conditions where
  tag := "LL32-SR"
  deps := [``RigidBody]

/-- Rotations about the largest and smallest principal axes are stable under small perturbations;
    rotation about the intermediate axis is unstable (tennis-racket effect). -/
informal_lemma intermediate_axis_instability where
  tag := "LL32-IAI"
  deps := [``RigidBody]

/-- If a rigid body is confined to planar motion, its dynamics reduce to a two-dimensional problem:
    the inertia reduces to a scalar moment and rotation is described
    by a single angular velocity. -/
informal_lemma reduction_to_two_body where
  tag := "LL32-RTB"
  deps := [``RigidBody]

/-- The power delivered to a rigid body by forces is P = ∑ Fᵢ ⋅ vᵢ = F_tot ⋅ V + M ⋅ ω, where F_tot
    is total force, V the reference point velocity, and M the torque. Translational and rotational
    contributions separate. -/
informal_lemma rigid_body_work_and_power where
  tag := "LL32-WP"
  deps := [``RigidBody]

/-- Small oscillations about a stable equilibrium orientation are governed by linearised equations
    obtained by expanding energy to second order in angular displacements. Normal modes and
    frequencies depend on inertia and restoring torques. -/
informal_lemma small_oscillations_about_equilibrium where
  tag := "LL32-SO"
  deps := [``RigidBody]

end RigidBody
