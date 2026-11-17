/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaneal Sajan, Joseph Tooby-Smith, Lode Vermeulen
-/
module

public import Physlib.ClassicalMechanics.HarmonicOscillator.Basic
/-!

# The initial conditions

## i. Overview

We define the type of initial conditions for the harmonic oscillator.
The initial conditions are currently defined as an initial position and an initial velocity,
that is the values of the solution and its time derivative at time `0`.

## ii. Key results

- `toInitialConditions`: Convert initial conditions at time `t₀` to standard initial conditions
  at `t=0`.
- `InitialConditionsFromTwoPositionstoInitialCondition`: Convert two-position initial conditions
  to standard initial conditions at `t = 0`.
- `InitialConditionsFromTwoVelocities.toInitialConditions`: Convert two-velocity initial
  conditions to standard initial conditions at `t = 0`.
- `x₀_zero`: The zero initial condition has zero starting point. : x₀ 0 = 0 := rfl
- `lemma v₀_zero`: The zero initial condition has zero starting velocity.

## iii. Table of contents
- A. Definition of the initial conditions
- B. Relation to other types of initial conditions
  - B.1. Initial conditions at arbitrary time
  - B.2. Initial conditions from two positions at different times
  - B.3. Initial conditions from two velocities at different times
- C. The zero initial conditions
  - C.1. Simple results for the zero initial conditions

## iv. References

References for the classical harmonic oscillator include:

* Landau & Lifshitz, Mechanics, page 58, section 21. [ref: landau_mechanics]
-/

TODO "Review the documentation in this file so the physical context of each initial-data choice is
clear. Reduce repeated mathematical explanations and derivations where they obscure that context."

@[expose] public

noncomputable section

namespace ClassicalMechanics.HarmonicOscillator

open Real

/-!

## A. Definition of the initial conditions

We start by defining the type of initial conditions for the harmonic oscillator.

-/

/-- The initial conditions for the harmonic oscillator specified by an initial position,
  and an initial velocity.

The `@[ext]` attribute provides an extensionality lemma for `InitialConditions`.
That is, a lemma which states that two initial conditions are equal if their
initial positions and initial velocities are equal. -/
@[ext] structure InitialConditions where
  /-- The initial position of the harmonic oscillator. -/
  x₀ : EuclideanSpace ℝ (Fin 1)
  /-- The initial velocity of the harmonic oscillator. -/
  v₀ : EuclideanSpace ℝ (Fin 1)

/-!

## B. Relation to other types of initial conditions

We relate the initial condition given by an initial position and an initial velocity
to other specifications of initial conditions.

In this section, we implement alternative ways to specify initial conditions for the harmonic
oscillator. The standard `InitialConditions` type specifies position and velocity at time `t=0`,
but in practice it is often useful to specify initial conditions at other times or in other forms.

Currently implemented:
- **Initial conditions at arbitrary time**: Specify position and velocity at any time `t₀`,
  not necessarily at `t=0`.
  This is useful for problems where the natural reference time is not zero.
- **Initial conditions from two positions at different times**: Specify the position at two
  distinct times `t₁` and `t₂` that satisfy the non-degeneracy condition.
- **Initial conditions from two velocities at different times**: Specify the velocity at two
  distinct times `t₁` and `t₂` that satisfy the non-degeneracy condition.
- **Amplitude–phase parametrization**: Specify the solution as a single shifted cosine
  `x(t) = A cos (ω t - φ)` with amplitude `A` and phase `φ`.

All alternative forms can be converted to the standard `InitialConditions` type via conversion
functions, and we prove that the converted initial conditions produce trajectories that satisfy
the original specifications.

-/

/-!

### B.1. Initial conditions at arbitrary time

We define a type for initial conditions specified at an arbitrary time `t₀`, rather than at `t=0`.
This is useful when the natural reference point for a problem is not at time zero.

The conversion to the standard `InitialConditions` works by "running the trajectory backward in
time" from `t₀` to `0`. Given that we know `x(t₀)` and `v(t₀)`, we use the harmonic oscillator
solution formula with time-reversal to determine what `x(0)` and `v(0)` must have been.

Mathematically, if `x(t) = cos(ωt)·x₀ + (sin(ωt)/ω)·v₀`, then setting `t = t₀`:
  `x(t₀) = cos(ωt₀)·x₀ + (sin(ωt₀)/ω)·v₀`
  `v(t₀) = -ω·sin(ωt₀)·x₀ + cos(ωt₀)·v₀`

Solving this linear system for `x₀` and `v₀` gives the formulas in `toInitialConditions` below.

-/

/-- Initial conditions for the harmonic oscillator specified at an arbitrary time `t₀`.

  This structure allows specifying the position and velocity at any time `t₀`, not necessarily
  at `t=0`. This is useful for problems where the natural reference time is not zero.

  The conditions can be converted to the standard `InitialConditions` format (at `t=0`)
  using the `toInitialConditions` function. -/
@[ext] structure InitialConditionsAtTime where
  /-- The time at which the initial conditions are specified. -/
  t₀ : Time
  /-- The position at time t₀. -/
  xT₀ : EuclideanSpace ℝ (Fin 1)
  /-- The velocity at time t₀. -/
  vT₀ : EuclideanSpace ℝ (Fin 1)

namespace InitialConditionsAtTime

/-- Convert initial conditions at time `t₀` to standard initial conditions at `t=0`.

  This conversion uses the harmonic oscillator solution formula with time-reversal.
  The resulting `InitialConditions` will produce a trajectory that passes through
  `xT₀` with velocity `vT₀` at time `t₀`.

  See `toInitialConditions_trajectory_at_t₀` and `toInitialConditions_velocity_at_t₀` for
  the correctness proofs. -/
noncomputable def toInitialConditions (S : HarmonicOscillator)
    (IC : InitialConditionsAtTime) : InitialConditions where
  x₀ := cos (S.ω * IC.t₀) • IC.xT₀ - (sin (S.ω * IC.t₀) / S.ω) • IC.vT₀
  v₀ := S.ω • sin (S.ω * IC.t₀) • IC.xT₀ + cos (S.ω * IC.t₀) • IC.vT₀

/-!
The correctness proofs showing that the conversion produces the expected trajectory
are given later in section D.1, after the trajectory machinery has been defined.
-/

end InitialConditionsAtTime


/-!

### B.2. Initial conditions from two positions at different times

We define a type for initial conditions specified by two measured positions `xT₁` and `xT₂`
at two distinct times `t₁` and `t₂`.

The conversion to the standard `InitialConditions` is obtained by solving for `x₀` and `v₀` the
two equations given by evaluating the trajectory at `t₁` and `t₂`:
  `xT₁ = cos(ωt₁)·x₀ + (sin(ωt₁)/ω)·v₀`
  `xT₂ = cos(ωt₂)·x₀ + (sin(ωt₂)/ω)·v₀`

This linear system has determinant `(cos(ωt₁)·sin(ωt₂) - cos(ωt₂)·sin(ωt₁))/ω = sin(ω(t₂-t₁))/ω`.
Writing `Δ = sin(ω(t₂-t₁))`, solving the system gives the formulas used below:
  `x₀ = (sin(ωt₂)·xT₁ - sin(ωt₁)·xT₂)/Δ`
  `v₀ = ω·(cos(ωt₁)·xT₂ - cos(ωt₂)·xT₁)/Δ`

The conversion is defined as a total function, but it recovers the initial conditions only when
`Δ = sin(ω(t₂-t₁)) ≠ 0`, i.e. when `t₂ - t₁` is not an integer multiple of half a period. The
correctness proofs, under this nondegeneracy condition, are given later in section D.2.

-/

/-- Initial conditions for the harmonic oscillator specified by two positions
  `xT₁` and `xT₂` measured at two times `t₁` and `t₂` respectively.

  The conditions can be converted to the standard `InitialConditions` format
  using the `toInitialConditions` function. -/
@[ext] structure InitialConditionsFromTwoPositions where
  /-- The first measurement time. -/
  t₁ : Time
  /-- The position at time `t₁`. -/
  xT₁ : EuclideanSpace ℝ (Fin 1)
  /-- The second measurement time. -/
  t₂ : Time
  /-- The position at time `t₂`. -/
  xT₂ : EuclideanSpace ℝ (Fin 1)


namespace InitialConditionsFromTwoPositions

/-- Convert two-position initial conditions to standard initial conditions at `t = 0`.

  Obtained by solving the 2×2 linear system from the trajectory formula at `t₁` and `t₂`.
  See `toInitialConditions_trajectory_at_t₁` and `toInitialConditions_trajectory_at_t₂` in
  section D.2 for the correctness proofs (valid under `sin (S.ω * (t₂ - t₁)) ≠ 0`). -/
noncomputable def toInitialConditions (S : HarmonicOscillator)
    (IC : InitialConditionsFromTwoPositions) : InitialConditions where
  x₀ := (sin (S.ω * IC.t₂) / sin (S.ω * (IC.t₂ - IC.t₁))) • IC.xT₁
      - (sin (S.ω * IC.t₁) / sin (S.ω * (IC.t₂ - IC.t₁))) • IC.xT₂
  v₀ := (S.ω * cos (S.ω * IC.t₁) / sin (S.ω * (IC.t₂ - IC.t₁))) • IC.xT₂
      - (S.ω * cos (S.ω * IC.t₂) / sin (S.ω * (IC.t₂ - IC.t₁))) • IC.xT₁

end InitialConditionsFromTwoPositions

/-!

### B.3. Initial conditions from two velocities at different times

We define a type for initial conditions specified by two measured velocities `vT₁` and `vT₂`
at two distinct times `t₁` and `t₂`.

The conversion to the standard `InitialConditions` is obtained by solving for `x₀` and `v₀` the
two equations given by evaluating the velocity of the trajectory at `t₁` and `t₂`:
  `vT₁ = -ω·sin(ωt₁)·x₀ + cos(ωt₁)·v₀`
  `vT₂ = -ω·sin(ωt₂)·x₀ + cos(ωt₂)·v₀`

This linear system has determinant `ω·(cos(ωt₁)·sin(ωt₂) - cos(ωt₂)·sin(ωt₁)) = ω·sin(ω(t₂-t₁))`.
Writing `Δ = sin(ω(t₂-t₁))`, solving the system gives the formulas used below:
  `x₀ = (cos(ωt₂)·vT₁ - cos(ωt₁)·vT₂)/(ω·Δ)`
  `v₀ = (sin(ωt₂)·vT₁ - sin(ωt₁)·vT₂)/Δ`

The conversion is defined as a total function, but it recovers the initial conditions only when
`Δ = sin(ω(t₂-t₁)) ≠ 0`, i.e. when `t₂ - t₁` is not an integer multiple of half a period. The
correctness proofs, under this nondegeneracy condition, are given later in section D.3.

-/

/-- Initial conditions for the harmonic oscillator specified by two velocities
  `vT₁` and `vT₂` measured at two times `t₁` and `t₂` respectively.

  The conditions can be converted to the standard `InitialConditions` format
  using the `toInitialConditions` function. -/
@[ext] structure InitialConditionsFromTwoVelocities where
  /-- The first measurement time. -/
  t₁ : Time
  /-- The velocity at time `t₁`. -/
  vT₁ : EuclideanSpace ℝ (Fin 1)
  /-- The second measurement time. -/
  t₂ : Time
  /-- The velocity at time `t₂`. -/
  vT₂ : EuclideanSpace ℝ (Fin 1)

namespace InitialConditionsFromTwoVelocities

/-- Convert two-velocity initial conditions to standard initial conditions at `t = 0`.

  Obtained by solving the 2×2 linear system from the velocity formula at `t₁` and `t₂`.
  See `toInitialConditions_velocity_at_t₁` and `toInitialConditions_velocity_at_t₂` in
  section D.3 for the correctness proofs (valid under `sin (S.ω * (t₂ - t₁)) ≠ 0`). -/
noncomputable def toInitialConditions (S : HarmonicOscillator)
    (IC : InitialConditionsFromTwoVelocities) : InitialConditions where
  x₀ := (cos (S.ω * IC.t₂) / (S.ω * sin (S.ω * (IC.t₂ - IC.t₁)))) • IC.vT₁
      - (cos (S.ω * IC.t₁) / (S.ω * sin (S.ω * (IC.t₂ - IC.t₁)))) • IC.vT₂
  v₀ := (sin (S.ω * IC.t₂) / sin (S.ω * (IC.t₂ - IC.t₁))) • IC.vT₁
      - (sin (S.ω * IC.t₁) / sin (S.ω * (IC.t₂ - IC.t₁))) • IC.vT₂

end InitialConditionsFromTwoVelocities

/-!

## C. The zero initial conditions

The zero initial conditions are the initial conditions with zero initial position
and zero initial velocity.

In the end, we will see that this corresponds to the solution which is identically zero,
i.e. the particle remains at rest at the origin.

-/

namespace InitialConditions

/-- The zero initial condition. -/
instance : Zero InitialConditions := ⟨0, 0⟩

/-!

### C.1. Simple results for the zero initial conditions

Some simple results about the zero initial conditions.

-/
/-- The zero initial condition has zero starting point. -/
@[simp]
lemma x₀_zero : x₀ 0 = 0 := rfl

/-- The zero initial condition has zero starting velocity. -/
@[simp]
lemma v₀_zero : v₀ 0 = 0 := rfl

end InitialConditions

end ClassicalMechanics.HarmonicOscillator
