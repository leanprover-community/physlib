/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.ClassicalMechanics.Pendulum.SimplePendulum.Geometric.Basic
public import Physlib.SpaceAndTime.Time.InnerProductSpace
/-!

# Geometric trajectories of the simple pendulum

## i. Overview

A trajectory of the simple pendulum is a time-parametrized curve in the configuration circle.
The dynamics of the pendulum is written for a real-valued lift of the angle;
`Trajectory.ofLift` sends such a lift to the trajectory it describes on the circle, by applying
the angular lift `ConfigurationSpace.ofAngle` at each time. Two lifts describe the same
trajectory exactly when at each time they differ by a whole number of turns, a smooth lift
describes a smooth curve in the circle, and composing with `ConfigurationSpace.toSpace` places
the bob in the plane along the trajectory, at distance `|ℓ|` from the pivot at all times.

The geometric velocity — the `mfderiv` of a trajectory as a tangent vector to the circle, read
in its stereographic charts — is left for a later module, as is the smooth identification of
the configuration space with `Circle`; in this module and the next, velocities are computed in
physical space, on the position of the bob in the plane.

## ii. Key results

- `Trajectory` : a trajectory of the pendulum, a curve in the configuration circle.
- `Trajectory.ofLift` : the trajectory described by a lift of the angle, with
  `Trajectory.ofLift_add_int_mul_two_pi` and `Trajectory.ofLift_eq_iff` making precise that two
  lifts describe the same trajectory exactly when they differ by whole turns at each time.
- `Trajectory.contMDiff_ofLift` : the trajectory described by a `C^n` lift is a `C^n` curve in
  the configuration circle; `Trajectory.continuous_ofLift` is the topological counterpart.
- `Trajectory.toSpace` : the physical position of the bob along a trajectory, with the
  rod-length constraint `Trajectory.norm_toSpace`.

## iii. Table of contents

- A. The trajectory type and the lift
- B. Smoothness of lifted trajectories
- C. Physical position along a trajectory

## iv. References

* `Physlib.ClassicalMechanics.Pendulum.SimplePendulum.Geometric.Basic` (the configuration circle,
  the angular lift `ofAngle` and the map to physical space).
* `Physlib.ClassicalMechanics.HarmonicOscillator.Geometric.Trajectory` (the corresponding trajectory
  module of the harmonic oscillator, whose structure this module follows).
-/

@[expose] public section

noncomputable section

open scoped Manifold

namespace ClassicalMechanics.SimplePendulum

/-!

## A. The trajectory type and the lift

A trajectory is a curve in the configuration circle, parametrized by `Time`. The dynamics is
written for the Euclidean lift `Time → EuclideanSpace ℝ (Fin 1)` of the angle; `ofLift` sends a
lift to the trajectory it describes, and the lift is faithful up to a whole number of turns at
each time: shifting a lift by `2π n` gives the same trajectory, and two lifts give the same
trajectory exactly when at each time they differ by some whole number of turns (possibly a
different number at different times).

-/

/-- A trajectory of the pendulum: a curve in the configuration space. -/
abbrev Trajectory := Time → ConfigurationSpace

namespace Trajectory

/-- The trajectory on the circle described by a lift `θ` of the angle. -/
def ofLift (θ : Time → EuclideanSpace ℝ (Fin 1)) : Trajectory := fun t =>
  ConfigurationSpace.ofAngle (θ t 0)

/-- At time `t` the trajectory described by a lift `θ` of the angle is the configuration at
  angle `θ t 0`. -/
lemma ofLift_apply (θ : Time → EuclideanSpace ℝ (Fin 1)) (t : Time) :
    ofLift θ t = ConfigurationSpace.ofAngle (θ t 0) := rfl

/-- Two lifts of the angle describe the same trajectory exactly when at each time they differ by
  a whole number of turns. -/
lemma ofLift_eq_iff (θ₁ θ₂ : Time → EuclideanSpace ℝ (Fin 1)) :
    ofLift θ₁ = ofLift θ₂ ↔ ∀ t, ∃ n : ℤ, θ₂ t 0 = θ₁ t 0 + n * (2 * Real.pi) := by
  simp only [funext_iff, ofLift_apply, ConfigurationSpace.ofAngle_eq_iff]

/-- Shifting a lift of the angle by a whole number of turns leaves the described trajectory
  unchanged. -/
lemma ofLift_add_int_mul_two_pi (θ : Time → EuclideanSpace ℝ (Fin 1)) (n : ℤ) :
    ofLift (fun t => θ t + (n * (2 * Real.pi)) • EuclideanSpace.single 0 1) = ofLift θ := by
  rw [ofLift_eq_iff]
  intro
  exact ⟨-n, by simp⟩

/-!

## B. Smoothness of lifted trajectories

The angular lift `ConfigurationSpace.ofAngle` is analytic, so the trajectory described by a lift
inherits the regularity of the lift: a continuous lift describes a continuous trajectory, and a
`C^n` lift describes a `C^n` curve in the configuration circle. Since `Time` is a normed space,
smoothness of the lift is ordinary `ContDiff` smoothness, while smoothness of the trajectory is
manifold smoothness into the circle.

-/

/-- The trajectory described by a continuous lift of the angle is continuous. -/
lemma continuous_ofLift {θ : Time → EuclideanSpace ℝ (Fin 1)} (hθ : Continuous θ) :
    Continuous (ofLift θ) :=
  ConfigurationSpace.continuous_ofAngle.comp
    ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp hθ)

/-- The trajectory described by a `C^n` lift of the angle is a `C^n` curve in the configuration
  circle. -/
lemma contMDiff_ofLift {n : WithTop ℕ∞} {θ : Time → EuclideanSpace ℝ (Fin 1)}
    (hθ : ContDiff ℝ n θ) : ContMDiff 𝓘(ℝ, Time) (𝓡 1) n (ofLift θ) := by
  apply (ConfigurationSpace.contMDiff_ofAngle.of_le le_top).comp (contMDiff_iff_contDiff.mpr _)
  exact (ContinuousLinearMap.contDiff (𝕜 := ℝ) (EuclideanSpace.proj (0 : Fin 1))).comp hθ

/-!

## C. Physical position along a trajectory

Composing a trajectory with the map to physical space places the bob in the plane at each time.
Along the trajectory described by a lift the bob is at `(ℓ sin θ, -ℓ cos θ)`, and the rod-length
constraint holds at all times: the bob stays on the circle of radius `|ℓ|` about the pivot.

-/

/-- The physical position of the bob along a trajectory, over time, for a rod of length `ℓ`. -/
def toSpace (ℓ : ℝ) (γ : Trajectory) (t : Time) : Space 2 := (γ t).toSpace ℓ

/-- Along the trajectory described by a lift `θ` of the angle the bob is at
  `(ℓ sin (θ t 0), -ℓ cos (θ t 0))`. -/
lemma toSpace_ofLift (ℓ : ℝ) (θ : Time → EuclideanSpace ℝ (Fin 1)) (t : Time) :
    toSpace ℓ (ofLift θ) t = ⟨![ℓ * Real.sin (θ t 0), -ℓ * Real.cos (θ t 0)]⟩ :=
  ConfigurationSpace.toSpace_ofAngle ℓ (θ t 0)

/-- The rod-length constraint along a trajectory: the bob stays at distance `|ℓ|` from the
  pivot. -/
lemma norm_toSpace (ℓ : ℝ) (γ : Trajectory) (t : Time) : ‖toSpace ℓ γ t‖ = |ℓ| :=
  ConfigurationSpace.toSpace_norm ℓ (γ t)

/-- The physical position of the bob along a continuous trajectory depends continuously on the
  time. -/
lemma continuous_toSpace (ℓ : ℝ) {γ : Trajectory} (hγ : Continuous γ) :
    Continuous (toSpace ℓ γ) :=
  (ConfigurationSpace.continuous_toSpace ℓ).comp hγ

end ClassicalMechanics.SimplePendulum.Trajectory

end
