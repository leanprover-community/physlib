/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaneal Sajan, Joseph Tooby-Smith, Lode Vermeulen
-/
module

public import Physlib.ClassicalMechanics.HarmonicOscillator.Solution.AmplitudePhase

/-!
# Special conditions of the trajectory

## i. Overview

We demonstrate particular results about solution trajectories such as return times and points when
the position or veliocity becomes zero

## ii. Key results

- `TempDistElectromagneticPotential`: The type of electromagnetic potentials as distributions.
- `trajectory_eq_cos` shows that on converting the initial conditions to amplitude-phase form
  and `trajectory_velocity_eq_sin`: Similarly, the velocity is a shifted sine.
- There are 2 results showing that the velocity vanishes when the sine has value zero.
  `trajectory_velocity_eq_zero_iff_sin_eq_zero`: Velocity is 0 when the solution sine is zero.
  `lemma trajectory_velocity_eq_zero_iff_exists_int`: Velocity is 0 when the phase is a multiple
  of pi.
- `trajectory_velocity_eq_zero_iff_norm_eq_amplitude`: The velocity vanishes when the trajectory
  has norm equal to the amplitude, i.e. when it is at an extremum of position.
- `trajectory_eq_zero_iff_cos_eq_zero`: The trajectory passes through zero when the
  cosine factor in amplitude-phase form vanishes and `trajectory_eq_zero_iff_exists_int` shows that
  the trajectory passes through zero when the phase is a half-odd-integer multiple of pi.

## iii. Table of contents
- A. Normal form for standard initial conditions
- B. Times at which the velocity is zero
- C. The position when the velocity is zero
- D. Times at which the trajectory passes through zero

## iv. References

References for the classical harmonic oscillator include:

* Landau & Lifshitz, Mechanics, page 58, section 21. [ref: landau_mechanics]

-/

@[expose] public

noncomputable section

namespace ClassicalMechanics.HarmonicOscillator

open Real Time

variable (S : HarmonicOscillator)

/-!

## A. Normal form for standard initial conditions

The amplitude-phase normal form was first proved for data already expressed as an
`AmplitudePhase`. We now transport those identities back to ordinary `InitialConditions` using
`AmplitudePhase.fromInitialConditions`.

-/

/-- Every trajectory of the harmonic oscillator is a single shifted cosine after converting its
  initial conditions to amplitude-phase form. -/
lemma trajectory_eq_cos (IC : InitialConditions) (t : Time) :
    IC.trajectory S t =
      EuclideanSpace.single 0 ((AmplitudePhase.fromInitialConditions S IC).A *
        cos (S.ω * t - (AmplitudePhase.fromInitialConditions S IC).φ)) := by
  conv_lhs =>
    rw [← AmplitudePhase.toInitialConditions_fromInitialConditions S IC]
  exact AmplitudePhase.toInitialConditions_trajectory_eq_cos S
    (AmplitudePhase.fromInitialConditions S IC) t

/-- The velocity of every trajectory is the corresponding shifted sine in amplitude-phase form. -/
lemma trajectory_velocity_eq_sin (IC : InitialConditions) (t : Time) :
    ∂ₜ (IC.trajectory S) t =
      EuclideanSpace.single 0 (-((AmplitudePhase.fromInitialConditions S IC).A * S.ω *
        sin (S.ω * t.val - (AmplitudePhase.fromInitialConditions S IC).φ))) := by
  conv_lhs =>
    rw [← AmplitudePhase.toInitialConditions_fromInitialConditions S IC]
  exact AmplitudePhase.toInitialConditions_velocity_eq_sin S
    (AmplitudePhase.fromInitialConditions S IC) t

/-!

## B. Times at which the velocity is zero

In amplitude-phase form the velocity is `v(t) = -Aω sin (ω t - φ)`. For nonzero amplitude this
vanishes exactly when `sin (ω t - φ) = 0`, equivalently when `ω t - φ` is an
integer multiple of `π`.

-/

/-- For nonzero amplitude, the velocity vanishes exactly when the sine factor in
  amplitude-phase form vanishes. -/
lemma trajectory_velocity_eq_zero_iff_sin_eq_zero (IC : InitialConditions)
    (hA : (AmplitudePhase.fromInitialConditions S IC).A ≠ 0) (t : Time) :
    ∂ₜ (IC.trajectory S) t = 0 ↔
      sin (S.ω * t.val - (AmplitudePhase.fromInitialConditions S IC).φ) = 0 := by
  rw [trajectory_velocity_eq_sin]
  simp [hA, S.ω_ne_zero]

/-- For nonzero amplitude, the velocity is zero exactly at phase times `φ + nπ`. -/
lemma trajectory_velocity_eq_zero_iff_exists_int (IC : InitialConditions)
    (hA : (AmplitudePhase.fromInitialConditions S IC).A ≠ 0) (t : Time) :
    ∂ₜ (IC.trajectory S) t = 0 ↔
      ∃ n : ℤ,
        (t : ℝ) =
          ((AmplitudePhase.fromInitialConditions S IC).φ + n * π) / S.ω := by
  rw [trajectory_velocity_eq_zero_iff_sin_eq_zero S IC hA t]
  constructor
  · intro h
    obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp h
    refine ⟨n, ?_⟩
    rw [eq_div_iff S.ω_ne_zero, mul_comm]
    linarith
  · rintro ⟨n, hn⟩
    rw [Real.sin_eq_zero_iff, hn]
    refine ⟨n, ?_⟩
    field_simp [S.ω_ne_zero]
    ring

/-!

## C. The position when the velocity is zero

The zeros of the velocity are the turning points of the oscillator. In amplitude-phase form,
these are the times when `sin (ω t - φ) = 0`; equivalently, `cos (ω t - φ)` is `1` or `-1`.
At exactly those times the trajectory has maximal norm, equal to the amplitude `A`.

The statement also covers the degenerate case `A = 0`: then the trajectory and its velocity are
identically zero, so both sides of the equivalence hold at every time.

-/

/-- The velocity vanishes exactly when the trajectory has norm equal to the amplitude. -/
lemma trajectory_velocity_eq_zero_iff_norm_eq_amplitude (IC : InitialConditions)
    (t : Time) :
    ∂ₜ (IC.trajectory S) t = 0 ↔
      ‖IC.trajectory S t‖ = (AmplitudePhase.fromInitialConditions S IC).A := by
  by_cases hA : (AmplitudePhase.fromInitialConditions S IC).A = 0
  · rw [trajectory_velocity_eq_sin, trajectory_eq_cos]
    simp [hA]
  rw [trajectory_velocity_eq_zero_iff_sin_eq_zero S IC hA t, trajectory_eq_cos]
  set A := (AmplitudePhase.fromInitialConditions S IC).A
  set θ := S.ω * t.val - (AmplitudePhase.fromInitialConditions S IC).φ
  show sin θ = 0 ↔ ‖EuclideanSpace.single 0 (A * cos θ)‖ = A
  have hA' : A ≠ 0 := by simpa [A] using hA
  have hA_nonneg : 0 ≤ A := norm_nonneg (⟨IC.x₀ 0, IC.v₀ 0 / S.ω⟩ : ℂ)
  have hA_pos : 0 < A := lt_of_le_of_ne hA_nonneg (Ne.symm hA')
  constructor
  · intro hsin
    rcases Real.sin_eq_zero_iff_cos_eq.mp hsin with hcos | hcos <;>
      simp [hcos, abs_of_pos hA_pos]
  · intro hnorm
    have hnorm' : |A * cos θ| = A := by
      simpa using hnorm
    have hcos_abs : |cos θ| = 1 := by
      rw [abs_mul, abs_of_pos hA_pos] at hnorm'
      exact mul_left_cancel₀ hA' (hnorm'.trans (mul_one A).symm)
    obtain ⟨n, hn⟩ := Real.abs_cos_eq_one_iff.mp hcos_abs
    exact Real.sin_eq_zero_iff.mpr ⟨n, hn⟩

/-!

## D. Times at which the trajectory passes through zero

In amplitude-phase form the trajectory is `x(t) = A cos (ω t - φ).` For nonzero amplitude this
vanishes exactly when `cos (ω t - φ) = 0`, equivalently when the phase is an odd multiple
of `π / 2`.

-/

/-- For nonzero amplitude, the trajectory passes through zero exactly when the cosine factor in
  amplitude-phase form vanishes. -/
lemma trajectory_eq_zero_iff_cos_eq_zero (IC : InitialConditions)
    (hA : (AmplitudePhase.fromInitialConditions S IC).A ≠ 0) (t : Time) :
    IC.trajectory S t = 0 ↔
      cos (S.ω * t.val - (AmplitudePhase.fromInitialConditions S IC).φ) = 0 := by
  rw [trajectory_eq_cos]
  simp [hA]

/-- For nonzero amplitude, the trajectory passes through zero exactly at phase times
  `φ + (2n + 1)π / 2`. -/
lemma trajectory_eq_zero_iff_exists_int (IC : InitialConditions)
    (hA : (AmplitudePhase.fromInitialConditions S IC).A ≠ 0) (t : Time) :
    IC.trajectory S t = 0 ↔
      ∃ n : ℤ,
        (t : ℝ) =
          ((AmplitudePhase.fromInitialConditions S IC).φ + (2 * n + 1) * π / 2) / S.ω := by
  rw [trajectory_eq_zero_iff_cos_eq_zero S IC hA t]
  constructor
  · intro h
    obtain ⟨n, hn⟩ := Real.cos_eq_zero_iff.mp h
    refine ⟨n, ?_⟩
    rw [eq_div_iff S.ω_ne_zero, mul_comm]
    linarith
  · rintro ⟨n, hn⟩
    rw [Real.cos_eq_zero_iff, hn]
    refine ⟨n, ?_⟩
    field_simp [S.ω_ne_zero]
    ring

end ClassicalMechanics.HarmonicOscillator
