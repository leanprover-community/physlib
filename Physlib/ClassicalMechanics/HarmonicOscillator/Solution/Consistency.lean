/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaneal Sajan, Joseph Tooby-Smith, Lode Vermeulen
-/
module

public import Physlib.ClassicalMechanics.HarmonicOscillator.Solution.Basic

/-!

# Consistency of the initial conditions

## i. Overview

Demonstrate that the different choices of initial conditions are self-consistent

## ii. Key results

- `InitialConditionsAtTime.toInitialConditions_trajectory_at_t₀`: The initial conditions specified
  at a point in time create trajectories that pass through the correct point.
  `InitialConditionsAtTime.toInitialConditions_velocity_at_t₀`: The initial conditions specified
  at a point in time create trajectories that pass through the initial point with the correct
  velocity.
  `InitialConditionsAtTime.toInitialConditions_energy_at_t₀`: The initial conditions specified
  at a point in time create trajectories that pass through the initial point with the correct
  energy.
- `InitialConditionsFromTwoPositions.toInitialConditions_trajectory_at_t₁`: Check that when the
  initial conditions are specified with two (time, position) pairs that the resulting
  trajectory has the correct position at the first of the two specified points.
  `InitialConditionsFromTwoPositions.toInitialConditions_trajectory_at_t₂`: As above for the
  second specified point.
- `InitialConditionsFromTwoVelocities.toInitialConditions_velocity_at_t₁`: Check that when the
  initial conditions are specified with two (time, velocity) pairs that the resulting
  trajectory has the correct velocity at the first of the two specified points.
  `InitialConditionsFromTwoVelocities.toInitialConditions_velocity_at_t₂`: As above for the
  second specified point.

## iii. Table of contents
- A. Correctness of Initial Conditions
  - A.1. Correctness of InitialConditionsAtTime conversion
  - A.2. Correctness of InitialConditionsFromTwoPositions conversion
  - A.3. Correctness of InitialConditionsFromTwoVelocities conversion

## iv. References

References for the classical harmonic oscillator include:

* Landau & Lifshitz, Mechanics, page 58, section 21. [ref: landau_mechanics]
-/

TODO "Review whether the initial-condition consistency lemmas in this file belong with the
corresponding trajectory or special-point results. Move overlapping results to the appropriate
module and namespace, preserve any distinct results, then remove `Consistency.lean` and update
its imports."

@[expose] public

noncomputable section

open Real Time ContDiff

variable (S : HarmonicOscillator)

namespace ClassicalMechanics.HarmonicOscillator

/-!

## A. Correctness of Initial Conditions

We now prove the correctness lemmas for the `InitialConditionsAtTime.toInitialConditions`
conversion function. These show that the conversion produces a trajectory that passes through
the specified position and velocity at the specified time.

-/

/-!

### A.1. Correctness of InitialConditionsAtTime conversion

-/

namespace InitialConditionsAtTime

/-- The trajectory resulting from `toInitialConditions` passes through the specified
  position `xT₀` at time `t₀`. -/
@[simp]
lemma toInitialConditions_trajectory_at_t₀ (S : HarmonicOscillator)
    (IC : InitialConditionsAtTime) :
    (IC.toInitialConditions S).trajectory S IC.t₀ = IC.xT₀ := by
  rw [InitialConditions.trajectory_eq, toInitialConditions]
  ext i
  simp only [smul_add, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
  field_simp [S.ω_ne_zero]
  linear_combination (S.ω * IC.xT₀.ofLp i) * cos_sq_add_sin_sq (S.ω * IC.t₀.val)

/-- The trajectory resulting from `toInitialConditions` has the specified
  velocity `vT₀` at time `t₀`. -/
@[simp]
lemma toInitialConditions_velocity_at_t₀ (S : HarmonicOscillator)
    (IC : InitialConditionsAtTime) :
    ∂ₜ ((IC.toInitialConditions S).trajectory S) IC.t₀ = IC.vT₀ := by
  rw [InitialConditions.trajectory_velocity, toInitialConditions]
  ext i
  simp only [neg_smul, smul_add, PiLp.add_apply, PiLp.neg_apply, PiLp.smul_apply, PiLp.sub_apply,
    smul_eq_mul]
  field_simp [S.ω_ne_zero]
  linear_combination (IC.vT₀.ofLp i) * cos_sq_add_sin_sq (S.ω * IC.t₀.val)

/-- The energy of the trajectory at time `t₀` equals the energy computed from the
  initial conditions at `t₀`. -/
lemma toInitialConditions_energy_at_t₀ (S : HarmonicOscillator)
    (IC : InitialConditionsAtTime) :
    S.energy ((IC.toInitialConditions S).trajectory S) IC.t₀ =
    1/2 * (S.m * ‖IC.vT₀‖^2 + S.k * ‖IC.xT₀‖^2) := by
  unfold energy kineticEnergy potentialEnergy
  simp only [toInitialConditions_trajectory_at_t₀, toInitialConditions_velocity_at_t₀]
  simp only [real_inner_self_eq_norm_sq, smul_eq_mul]
  ring

end InitialConditionsAtTime

/-!

### A.2. Correctness of InitialConditionsFromTwoPositions conversion

The conversion recovers the initial conditions only when `sin (S.ω * (t₂ - t₁)) ≠ 0`. This
condition fails exactly when `ω·(t₂ - t₁) = n·π` for some integer `n`, i.e. when `t₂ - t₁` is an
integer multiple of half a period; in that case `x(t₂) = (-1)^n · x(t₁)` for every trajectory,
independent of `v₀`, so the two positions do not determine the initial conditions.

Under this nondegeneracy condition, we prove that the resulting trajectory passes through `xT₁`
at `t₁` and `xT₂` at `t₂`.

-/

namespace InitialConditionsFromTwoPositions

/-- The trajectory from `toInitialConditions` passes through `xT₁` at time `t₁`,
  provided `sin (S.ω * (t₂ - t₁)) ≠ 0`. -/
lemma toInitialConditions_trajectory_at_t₁ (S : HarmonicOscillator)
    (IC : InitialConditionsFromTwoPositions)
    (hΔ : sin (S.ω * (IC.t₂ - IC.t₁)) ≠ 0) :
    (IC.toInitialConditions S).trajectory S IC.t₁ = IC.xT₁ := by
  rw [InitialConditions.trajectory_eq, toInitialConditions]
  ext i
  simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
  field_simp [S.ω_ne_zero]
  grind [mul_sub, Real.sin_sub]

/-- The trajectory from `toInitialConditions` passes through `xT₂` at time `t₂`,
  provided `sin (S.ω * (t₂ - t₁)) ≠ 0`. -/
lemma toInitialConditions_trajectory_at_t₂ (S : HarmonicOscillator)
    (IC : InitialConditionsFromTwoPositions)
    (hΔ : sin (S.ω * (IC.t₂ - IC.t₁)) ≠ 0) :
    (IC.toInitialConditions S).trajectory S IC.t₂ = IC.xT₂ := by
  rw [InitialConditions.trajectory_eq, toInitialConditions]
  ext i
  simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
  field_simp [S.ω_ne_zero]
  grind [mul_sub, Real.sin_sub]

end InitialConditionsFromTwoPositions

/-!

### A.3. Correctness of InitialConditionsFromTwoVelocities conversion

The conversion recovers the initial conditions only when `sin (S.ω * (t₂ - t₁)) ≠ 0`. Under this
nondegeneracy condition, we prove that the resulting trajectory has velocity `vT₁` at `t₁` and
`vT₂` at `t₂`.

-/

namespace InitialConditionsFromTwoVelocities

/-- The trajectory from `toInitialConditions` has velocity `vT₁` at time `t₁`,
  provided `sin (S.ω * (t₂ - t₁)) ≠ 0`. -/
lemma toInitialConditions_velocity_at_t₁ (S : HarmonicOscillator)
    (IC : InitialConditionsFromTwoVelocities)
    (hΔ : sin (S.ω * (IC.t₂ - IC.t₁)) ≠ 0) :
    ∂ₜ ((IC.toInitialConditions S).trajectory S) IC.t₁ = IC.vT₁ := by
  rw [InitialConditions.trajectory_velocity, toInitialConditions]
  ext i
  simp only [neg_smul, PiLp.add_apply, PiLp.neg_apply, PiLp.smul_apply, PiLp.sub_apply,
    smul_eq_mul]
  field_simp [S.ω_ne_zero]
  grind [mul_sub, Real.sin_sub]

/-- The trajectory from `toInitialConditions` has velocity `vT₂` at time `t₂`,
  provided `sin (S.ω * (t₂ - t₁)) ≠ 0`. -/
lemma toInitialConditions_velocity_at_t₂ (S : HarmonicOscillator)
    (IC : InitialConditionsFromTwoVelocities)
    (hΔ : sin (S.ω * (IC.t₂ - IC.t₁)) ≠ 0) :
    ∂ₜ ((IC.toInitialConditions S).trajectory S) IC.t₂ = IC.vT₂ := by
  rw [InitialConditions.trajectory_velocity, toInitialConditions]
  ext i
  simp only [neg_smul, PiLp.add_apply, PiLp.neg_apply, PiLp.smul_apply, PiLp.sub_apply,
    smul_eq_mul]
  field_simp [S.ω_ne_zero]
  grind [mul_sub, Real.sin_sub]

end InitialConditionsFromTwoVelocities

end HarmonicOscillator

end ClassicalMechanics
