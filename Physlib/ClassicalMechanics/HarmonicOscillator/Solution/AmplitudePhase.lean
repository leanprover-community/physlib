/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaneal Sajan, Joseph Tooby-Smith, Lode Vermeulen
-/
module

public import Physlib.ClassicalMechanics.HarmonicOscillator.Solution.Basic

/-!
# Amplitude–phase parametrization

## i. Overview

The state of the harmonic oscillator at `t = 0` is captured by `InitialConditions` as a position
`x₀` and a velocity `v₀`. An equivalent and often more physical description writes the solution as
a single shifted cosine of amplitude `A` and phase `φ`:
  `x(t) = A cos (ω t - φ)`.

Expanding with the angle-subtraction identity,
  `A cos (ω t - φ) = (A cos φ) cos (ω t) + (A sin φ) sin (ω t)`,
and matching coefficients against the standard solution
  `x(t) = cos (ω t) x₀ + (sin (ω t) / ω) v₀`
gives the change of coordinates
  `x₀ = A cos φ`,   `v₀ = A ω sin φ`.

We implement the forward map `(A, φ) ↦ (x₀, v₀)` as `toInitialConditions`, prove the resulting
trajectory is the cosine normal form above (with velocity `-A ω sin (ω t - φ)`), and implement the
inverse map `(x₀, v₀) ↦ (A, φ)` as `fromInitialConditions`, recovering `A` and `φ` as the polar
coordinates of the phase vector `(x₀, v₀ / ω)`.

## ii. Key results

- `toInitialConditions`: Amplitude–phase initial conditions converted to standard
  initial conditions.
- `toInitialConditions_trajectory_eq_cos`: The trajectory of amplitude–phase initial conditions is
  the cosine normal form.
- `toInitialConditions_velocity_eq_sin`: The trajectory of amplitude–phase initial conditions is
  the sine normal form.
- `fromInitialConditions`: Amplitude–phase initial conditions from standard initial conditions.
- `toInitialConditions_fromInitialConditions`: Right inverse of `fromInitialConditions`.

## iii. Table of contents
- A. The amplitude–phase initial conditions
- B. Conversion to standard initial conditions
- C. The trajectory in normal form
- D. Recovering the amplitude and phase

## iv. References

References for the classical harmonic oscillator include:

* Landau & Lifshitz, Mechanics, page 58, section 21. [ref: landau_mechanics]
-/

@[expose] public noncomputable section

namespace ClassicalMechanics.HarmonicOscillator

open Real Time ContDiff

variable (S : HarmonicOscillator)

/-!

## A. The amplitude–phase initial conditions

We define a type for initial conditions specified by an amplitude `A` and a phase angle `φ`. Being
an amplitude and an angle, these are stored as scalars, rather than as vectors as for the other
initial-condition types.

-/

/-- Initial conditions for the harmonic oscillator specified by an amplitude `A` and a phase
  offset `φ`, describing the solution `x(t) = A cos (ω t - φ)`.

  The conditions can be converted to the standard `InitialConditions` format using the
  `toInitialConditions` function. -/
@[ext] structure AmplitudePhase where
  /-- The amplitude of the oscillation. -/
  A : ℝ
  /-- The phase offset of the oscillation. -/
  φ : ℝ

namespace AmplitudePhase

/-!

## B. Conversion to standard initial conditions

Using `x₀ = A cos φ` and `v₀ = A ω sin φ`, we convert amplitude–phase data to the standard initial
position and velocity at `t = 0`.

-/

/-- Convert amplitude–phase initial conditions to standard initial conditions at `t = 0`, via
  `x₀ = A cos φ` and `v₀ = A ω sin φ`.

  See `toInitialConditions_trajectory_eq_cos` and `toInitialConditions_velocity_eq_sin` in
  section E.3 for the correctness proofs. -/
noncomputable def toInitialConditions (S : HarmonicOscillator) (IC : AmplitudePhase) :
    InitialConditions where
  x₀ := EuclideanSpace.single 0 (IC.A * cos IC.φ)
  v₀ := EuclideanSpace.single 0 (IC.A * S.ω * sin IC.φ)

/-!

## C. The trajectory in normal form

The trajectory built from amplitude–phase data is exactly the single cosine
`x(t) = A cos (ω t - φ)`, with velocity `v(t) = -A ω sin (ω t - φ)`. In the position identity the
factor `1 / ω` of the standard solution cancels the `ω` in `v₀ = A ω sin φ`, which uses `ω ≠ 0`.

-/

/-- The trajectory of amplitude–phase initial conditions is the cosine normal form
  `x(t) = A cos (ω t - φ)`. -/
lemma toInitialConditions_trajectory_eq_cos (S : HarmonicOscillator) (IC : AmplitudePhase)
    (t : Time) :
    (IC.toInitialConditions S).trajectory S t
      = EuclideanSpace.single 0 (IC.A * cos (S.ω * t - IC.φ)) := by
  rw [InitialConditions.trajectory_eq, toInitialConditions]
  ext i
  fin_cases i
  simp [Real.cos_sub]
  field_simp [S.ω_ne_zero]

/-- The velocity of the amplitude–phase trajectory is `v(t) = -A ω sin (ω t - φ)`. -/
lemma toInitialConditions_velocity_eq_sin (S : HarmonicOscillator) (IC : AmplitudePhase)
    (t : Time) :
    ∂ₜ ((IC.toInitialConditions S).trajectory S) t
      = EuclideanSpace.single 0 (-(IC.A * S.ω * sin (S.ω * t.val - IC.φ))) := by
  rw [InitialConditions.trajectory_velocity, toInitialConditions]
  ext i
  fin_cases i
  simp [Real.sin_sub]
  ring

/-!

## D. Recovering the amplitude and phase

The inverse map `(x₀, v₀) ↦ (A, φ)` must solve `x₀ = A cos φ` and `v₀ / ω = A sin φ`. Recovering
the angle with the real `arctan` covers only `(-π/2, π/2)` and forces a case split at `x₀ = 0`; we
instead embed the phase vector as the complex number `z = x₀ + (v₀ / ω) i` and read off `A = ‖z‖`
and `φ = Complex.arg z`, with `arg` in the canonical range `(-π, π]`. The degenerate state
`x₀ = v₀ = 0` is covered by the convention `arg 0 = 0`, so no case split is needed.

We prove that converting initial conditions to amplitude–phase form and back returns the original
initial conditions.

-/

/-- Recover amplitude–phase data from standard initial conditions, as the polar coordinates of the
  phase vector `(x₀, v₀ / ω)` embedded as `z = x₀ + (v₀ / ω) i`: the amplitude is `‖z‖` and the
  phase is `Complex.arg z`.

  See `toInitialConditions_fromInitialConditions` for the right-inverse identity. -/
noncomputable def fromInitialConditions (S : HarmonicOscillator) (IC : InitialConditions) :
    AmplitudePhase where
  A := ‖(⟨IC.x₀ 0, IC.v₀ 0 / S.ω⟩ : ℂ)‖
  φ := Complex.arg (⟨IC.x₀ 0, IC.v₀ 0 / S.ω⟩ : ℂ)

/-- `fromInitialConditions` is a right inverse of `toInitialConditions`: converting initial
  conditions to amplitude–phase form and back recovers them exactly. -/
lemma toInitialConditions_fromInitialConditions (S : HarmonicOscillator)
    (IC : InitialConditions) :
    (fromInitialConditions S IC).toInitialConditions S = IC := by
  have hω : S.ω ≠ 0 := S.ω_ne_zero
  set z : ℂ := (⟨IC.x₀ 0, IC.v₀ 0 / S.ω⟩ : ℂ)
  -- polar identities
  have hcos : ‖z‖ * cos (Complex.arg z) = z.re := Complex.norm_mul_cos_arg z
  have hsin : ‖z‖ * sin (Complex.arg z) = z.im := Complex.norm_mul_sin_arg z
  -- By construction the parts of `z` are exactly the original data.
  have hre : z.re = IC.x₀ 0 := rfl
  have him : z.im = IC.v₀ 0 / S.ω := rfl
  apply InitialConditions.ext
  · -- Position: `‖z‖ cos (arg z) = Re z = IC.x₀ 0`, and `single 0 (IC.x₀ 0) = IC.x₀`.
    show EuclideanSpace.single 0 (‖z‖ * cos (Complex.arg z)) = IC.x₀
    rw [hcos, hre]
    ext i; fin_cases i; simp
  · -- Velocity: `‖z‖ ω sin (arg z) = ω · Im z = ω · (v₀ / ω) = IC.v₀ 0`, then reassemble.
    show EuclideanSpace.single 0 (‖z‖ * S.ω * sin (Complex.arg z)) = IC.v₀
    have hv : ‖z‖ * S.ω * sin (Complex.arg z) = IC.v₀ 0 := by
      rw [mul_right_comm, hsin, him]; field_simp
    rw [hv]
    ext i; fin_cases i; simp

end AmplitudePhase

end HarmonicOscillator

end ClassicalMechanics
