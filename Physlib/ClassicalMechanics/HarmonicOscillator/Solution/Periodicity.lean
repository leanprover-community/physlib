/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaneal Sajan, Joseph Tooby-Smith, Lode Vermeulen
-/
module

public import Physlib.ClassicalMechanics.HarmonicOscillator.Solution.Basic

/-!

# Periodicity and recurrence

## i. Overview

Every trajectory is a shifted cosine of angular frequency `ω`, so it repeats after a fixed period
`T = 2π / ω`. We record the period, show the trajectory is periodic, and prove that — for
non-trivial initial data — the trajectory returns to its initial position and velocity exactly at
integer multiples of the period.

## ii. Key results

- `period`: The oscillator period is the standard 2 pi / angular frequency.
- `period_eq`: The notation "T" corresponds to the period defined above.
- `period_pos`: The period is positive.
- `trajectory_periodic`: The trajectory of the harmonic oscillator is periodic with
  period of `2 * π / ω`.
- `return_time`: The oscillator returns to its starting point on integer multiples of its period.

## iii. Table of contents
- A. The period
- B. Periodicity of the trajectory
- C. Return to the initial state

## iv. References

References for the classical harmonic oscillator include:

* Landau & Lifshitz, Mechanics, page 58, section 21. [ref: landau_mechanics]

-/

@[expose] public

noncomputable section

namespace ClassicalMechanics.HarmonicOscillator

open Real Time ContDiff

variable (S : HarmonicOscillator)

/-!

## A. The period

The period `T = 2π / ω` is the time for one complete oscillation; it is positive since `ω > 0`.

-/

/--
The period of a harmonic oscillator is `2 * π / ω`.
-/
noncomputable def period (S : HarmonicOscillator) : ℝ := 2 * π / S.ω

@[inherit_doc period]
scoped notation "T" => HarmonicOscillator.period

lemma period_eq : T S = 2 * π / S.ω := rfl

lemma period_pos : 0 < T S := div_pos (by positivity) S.ω_pos

/-!

## B. Periodicity of the trajectory

The trajectory satisfies `x(t + T) = x(t)`: advancing time by one period shifts the phase `ω t`
by `2π`, leaving `cos` and `sin` unchanged.

-/

/--
The trajectory of the harmonic oscillator is periodic with period of `2 * π / ω`.
-/
lemma trajectory_periodic (IC : InitialConditions) :
    Function.Periodic (IC.trajectory S) (T S) := fun t ↦ by
  have h : S.ω * (t.val + 2 * π / S.ω) = S.ω * t.val + 2 * π := by
    have := S.ω_ne_zero
    ring_nf; field_simp
  rw [InitialConditions.trajectory, add_val, period_eq, h, cos_add_two_pi, sin_add_two_pi]
  rfl

/-!

## C. Return to the initial state

For non-trivial initial data, the trajectory returns to its initial position and velocity only at
integer multiples of the period.

-/

/--
Assuming that the initial coordinate and velocity are not simultaneously zero,
the time stamps when the harmonic oscillator returns to its initial coordinate and velocity is
a multiple of its period
-/
lemma return_time (IC : InitialConditions) (non_trivial : IC.x₀ ≠ 0 ∨ IC.v₀ ≠ 0)
    (t : Time) (ht : IC.trajectory S t = IC.x₀ ∧ ∂ₜ (IC.trajectory S) t = IC.v₀) :
    ∃ n : ℤ,  (n : ℝ) * (T S) = t := by
  have htx := ht.left
  have htv := ht.right
  rw [InitialConditions.trajectory_eq] at htx
  rw [InitialConditions.trajectory_velocity] at htv
  simp at htx
  simp at htv
  set c := cos (S.ω * t)
  set s :=  sin (S.ω * t)
  set xx := inner ℝ IC.x₀ IC.x₀
  set vv := inner ℝ IC.v₀ IC.v₀
  set xv := inner ℝ IC.x₀ IC.v₀
  set det := vv + xx *  S.ω^2
  have hxx0 : 0 ≤ xx := real_inner_self_nonneg
  have hvv0 : 0 ≤ vv := real_inner_self_nonneg
  have hω2 : 0 < S.ω ^ 2 := pow_pos S.ω_pos 2
  have zero_lt_det : 0 < det := by
    show 0 < vv + xx * S.ω ^ 2
    rcases non_trivial with hx | hv
    · nlinarith [real_inner_self_pos.mpr hx]
    · nlinarith [real_inner_self_pos.mpr hv]
  have det_ne_zero : det ≠ 0 := zero_lt_det.ne'
  have hxx : c * xx + (s / S.ω) * xv = xx := by
    have h := congrArg (inner ℝ IC.x₀) htx
    simpa only [inner_add_right, real_inner_smul_right] using h
  have hvv : - S.ω * s * xv + c * vv = vv := by
    have h := congrArg (fun w => inner ℝ w IC.v₀) htv
    simpa only [inner_add_left, inner_neg_left, real_inner_smul_left, neg_mul, mul_assoc] using h
  have hcos : 1 = cos (S.ω * t) := by
    calc
    1 =  det / det := by simp only [ne_eq, det_ne_zero, not_false_eq_true, div_self]
    _ = (vv + xx * S.ω^2 ) / det := by rfl
    _ = c * ((vv + xx * S.ω^2) / det) + s * xv *S.ω* (S.ω/S.ω-1 ) / det := by
      nth_rewrite 1 [← hvv, ← hxx]
      ring_nf
    _ = c * ((vv + xx * S.ω^2) / det ) := by
      simp only [ne_eq, S.ω_ne_zero, not_false_eq_true,
        div_self, sub_self, mul_zero, zero_div, add_zero]
    _ = c * (det / det) := by rfl
    _ = c := by simp only [ne_eq, det_ne_zero, not_false_eq_true, div_self, mul_one]
    _ = _ := by rfl
  obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff (S.ω * t)).mp hcos.symm
  refine ⟨n, ?_⟩
  rw [period_eq]
  field_simp [S.ω_ne_zero]
  linear_combination hn

end ClassicalMechanics.HarmonicOscillator
