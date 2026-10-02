/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.ClassicalMechanics.Pendulum.SimplePendulum.SmallAngle
public import Physlib.Mathematics.SpecialFunctions.EllipticIntegral
public import Physlib.Mathematics.ForMathlib.Trigonometry.SinSq
/-!

# The period formula of the simple gravity pendulum

## i. Overview

Beyond the small-angle approximation the period of the simple gravity pendulum depends on the
amplitude of the swing. Released from rest at the angle `θ₀`, with `0 < θ₀ < π`, the pendulum
librates about the bottom of its swing, and the classical calculation (Landau & Lifshitz, §11,
Problem 1) integrates the energy first integral by quadrature: the quarter period is the time
of descent from `θ₀` to the bottom, the substitution `sin (θ/2) = sin (θ₀/2) sin φ` turns the
resulting integral into a complete elliptic integral of the first kind, and the period is

`T = 4 √(ℓ/g) K(sin ½θ₀)`,

with `K` Legendre's complete elliptic integral of the first kind in the modulus convention. In
the parameter convention of `Real.completeEllipticK`, where the parameter is the square
`m = k²` of the modulus, the same formula reads `4 √(ℓ/g) completeEllipticK (sin² (θ₀/2))`.

This module records that formula as `SimplePendulum.periodFormula` and proves what follows
for it from the theory of `completeEllipticK` alone: it is even in the amplitude, at zero
amplitude it is the small-angle period `2π √(ℓ/g)`, it is continuous on `(-π, π)` and tends to
the small-angle period as the amplitude tends to zero, it is never below the small-angle
period, it is strictly increasing in the amplitude on `[0, π)`, and it is at most
`2π √(ℓ/g) / cos (θ₀/2)`. The formula is therefore not constant in the amplitude — the
classical statement that the pendulum is not isochronous, once the identification below is
proved — and the upper bound quantifies how it grows as the amplitude approaches the inverted
position.

What this module does not do is identify `periodFormula θ₀` with the period of a solution of
the nonlinear equation of motion released from rest at `θ₀`. That identification is the
theorem the formula is named for, and its formalization — the quarter period as a first hitting
time, the quadrature of the energy first integral, the substitution, and their assembly, on top
of the uniqueness of solutions and the time-reversal symmetry of the equation of motion
(formalized in the companion module `SimplePendulum/Solution.lean`) — is not yet carried out;
the `TODO` after the definition lists the milestones. The pointwise energy first integral itself,
`θ̇² = (2g/ℓ)(cos θ - cos θ₀)`, is now proved in the companion module
`SimplePendulum/ReleasedFromRest.lean`; turning it into the quarter period as a definite integral
remains open, along with the rest of the milestones below. Until then
`periodFormula` is a definition, and the statements about it are statements about the elliptic
integral.

## ii. Key results

- `SimplePendulum.periodFormula` is the classical formula `4 √(ℓ/g) K(sin² (θ₀/2))` for the
  period of libration with amplitude `θ₀`; for `|θ₀| < π` its parameter `sin² (θ₀/2)` lies
  below `1` (`Real.sin_half_sq_lt_one`), so it is evaluated on the domain of
  `completeEllipticK`.
- `SimplePendulum.periodFormula_neg`: the formula is even in the amplitude.
- `SimplePendulum.periodFormula_zero`: at zero amplitude the formula is the small-angle
  period, `periodFormula 0 = smallAnglePeriod`.
- `SimplePendulum.continuousOn_periodFormula` and
  `SimplePendulum.continuousAt_periodFormula_zero`: the formula is continuous on `(-π, π)`,
  in particular at `0`.
- `SimplePendulum.periodFormula_tendsto_smallAnglePeriod`: the formula tends to the
  small-angle period as the amplitude tends to zero.
- `SimplePendulum.periodFormula_mono` and `SimplePendulum.periodFormula_strictMono`, with the
  bundled `SimplePendulum.monotoneOn_periodFormula` and
  `SimplePendulum.strictMonoOn_periodFormula`: on `[0, π)` the formula is increasing, and
  strictly increasing, in the amplitude.
- `SimplePendulum.smallAnglePeriod_le_periodFormula` and `SimplePendulum.periodFormula_pos`:
  the formula is at least the small-angle period, in particular positive, whenever
  `sin² (θ₀/2) < 1`.
- `SimplePendulum.periodFormula_le` and `SimplePendulum.periodFormula_le'`: for `|θ₀| < π` the
  formula is at most `2π √(ℓ/g) / cos (θ₀/2) = smallAnglePeriod / cos (θ₀/2)`.

## iii. Table of contents

- A. The period formula, its continuity and its small-angle limit
  - A.1. The formula, its domain and its evenness
  - A.2. Continuity and the small-angle limit
- B. Monotonicity and bounds in the amplitude
  - B.1. Monotonicity in the amplitude
  - B.2. Bounds

## iv. References

* Landau & Lifshitz, Mechanics, 3rd ed., §11, Problem 1: `T = 4 √(l/g) K(sin ½φ₀)`, in the modulus
  convention `K(k) = ∫ φ in 0..π/2, (1 - k² sin² φ)^(-1/2)`. [ref: landau_mechanics]
* M. Abramowitz, I. A. Stegun, Handbook of Mathematical Functions, 17.3.1 (the parameter convention
  `K(m)`, `m = k²`, used by `Real.completeEllipticK`). [ref: abramowitz_stegun_1964]
* The module `Physlib.Mathematics.SpecialFunctions.EllipticIntegral`, for `completeEllipticK` and
  its theory on the domain `m < 1`.
* The module `Physlib.ClassicalMechanics.Pendulum.SimplePendulum.SmallAngle`, for the small-angle
  period `smallAnglePeriod = 2π √(ℓ/g)`.
-/

@[expose] public section

namespace ClassicalMechanics

namespace SimplePendulum

variable (S : SimplePendulum)

/-!

## A. The period formula, its continuity and its small-angle limit

The classical formula for the period of libration as a function of the amplitude, its evenness
and its domain, and its behaviour at small amplitudes: it is continuous on the libration range
`(-π, π)`, at zero amplitude it is exactly the small-angle period, and it tends to the
small-angle period as the amplitude tends to zero. These are facts about the elliptic integral
on its domain and at the parameter `0`, where `K 0 = π/2`.

-/

/-!

### A.1. The formula, its domain and its evenness

The formula `4 √(ℓ/g) K(sin² (θ₀/2))` is defined for every real `θ₀`, and is even in `θ₀`; for
libration amplitudes `|θ₀| < π` the parameter `sin² (θ₀/2)` is below `1`
(`Real.sin_half_sq_lt_one`), so the elliptic integral is evaluated on its domain. At `θ₀ = ±π`
the parameter is `1`, where Legendre's `K` diverges — the pendulum released from rest at the
inverted position never returns — while the Lean value of `completeEllipticK` at `m = 1` is a
junk value (see the module docstring of `Physlib.Mathematics.SpecialFunctions.EllipticIntegral`),
so nothing is claimed there.

-/

/-- The classical formula `4 √(ℓ/g) K(sin² (θ₀/2))` for the period of libration of the simple
  gravity pendulum with amplitude `θ₀` (Landau & Lifshitz, §11, Problem 1, where it is written
  `T = 4 √(l/g) K(sin ½φ₀)` in the modulus convention). Its identification with the return
  time of a solution of the nonlinear equation of motion is not yet formalized (see the
  TODO). -/
noncomputable def periodFormula (θ₀ : ℝ) : ℝ :=
  4 * √(S.ℓ / S.g) * Real.completeEllipticK (Real.sin (θ₀ / 2) ^ 2)

TODO "Prove that `periodFormula θ₀` is the period of the motion of the simple pendulum released
  from rest at the amplitude `θ₀`, for `0 < θ₀ < π`. Milestones 1–2 — the uniqueness of the
  smooth solutions of the equation of motion with given initial data, and the time-reversal
  symmetry of the equation of motion, so that the motion released from rest is even in time and
  its period is four times the time of descent to the bottom — are formalized in a companion
  module, `SimplePendulum/Solution.lean` (`SimplePendulum.equationOfMotion_unique`,
  `SimplePendulum.releasedFromRest_even`). The pointwise half of milestone 4, the energy first
  integral `θ̇² = (2g/ℓ)(cos θ - cos θ₀)`, is formalized in a further companion module,
  `SimplePendulum/ReleasedFromRest.lean`
  (`SimplePendulum.sq_deriv_eq_of_isSolution_of_deriv_zero'`); remaining:
  (3) the quarter period as the first hitting time of `θ = 0` by the motion released from rest,
  which needs the monotonicity of the descent from `θ₀` to `0` — not yet formalized — as an
  input;
  (4) turning the pointwise energy first integral above into the quarter period as a definite
  integral, `√(ℓ/(2g)) ∫ θ in 0..θ₀, (cos θ - cos θ₀)^(-1/2)`, by a change of variables from time
  to the angle along the (monotonic) descent;
  (5) the substitution `sin (θ/2) = sin (θ₀/2) sin φ`, which transforms that integral into
  `√(ℓ/g) completeEllipticK (sin² (θ₀/2))`, including the justification that the resulting
  improper integral, singular at `θ = θ₀`, converges;
  (6) the assembly of (1)–(5) into the theorem that the motion released from rest at `θ₀` is
  periodic with period `periodFormula θ₀`, which needs the motion to be defined for all time —
  only local existence (`SimplePendulum.exists_local_solution`) is formalized so far."

/-- The period formula is even in the amplitude, `periodFormula (-θ₀) = periodFormula θ₀`: its
  parameter `sin² (θ₀/2)` is even in `θ₀`. -/
lemma periodFormula_neg (θ₀ : ℝ) : S.periodFormula (-θ₀) = S.periodFormula θ₀ := by
  simp only [periodFormula, neg_div, Real.sin_neg, neg_sq]

/-!

### A.2. Continuity and the small-angle limit

At zero amplitude the parameter of the elliptic integral is `0`, where `K 0 = π/2`, and the
formula collapses to `4 √(ℓ/g) · π/2 = 2π √(ℓ/g)`: the small-angle period. Since `K` is
continuous on its domain and the parameter `sin² (θ₀/2)` is continuous in the amplitude and
stays below `1` for `|θ₀| < π`, the formula is continuous on `(-π, π)`; in particular it tends
to the small-angle period as the amplitude tends to zero — the sense in which the small-angle
theory of `SimplePendulum.SmallAngle` is the limit of the classical formula.

-/

/-- At zero amplitude the period formula is the small-angle period: `K 0 = π/2` turns
  `4 √(ℓ/g) K 0` into `2π √(ℓ/g)`. -/
@[simp]
lemma periodFormula_zero : S.periodFormula 0 = S.smallAnglePeriod := by
  rw [periodFormula, smallAnglePeriod_eq, zero_div, Real.sin_zero, zero_pow two_ne_zero,
    Real.completeEllipticK_zero]
  ring

/-- The period formula is continuous on the libration range `(-π, π)`: `completeEllipticK` is
  continuous at every parameter `m < 1`, and the parameter `sin² (θ₀/2)` is continuous in `θ₀`
  and below `1` for `|θ₀| < π`. -/
lemma continuousOn_periodFormula : ContinuousOn S.periodFormula (Set.Ioo (-Real.pi) Real.pi) := by
  refine continuousOn_of_forall_continuousAt fun θ₀ hθ₀ => ?_
  have hp : ContinuousAt (fun θ : ℝ => Real.sin (θ / 2) ^ 2) θ₀ := by fun_prop
  have hK : ContinuousAt Real.completeEllipticK (Real.sin (θ₀ / 2) ^ 2) :=
    Real.continuousAt_completeEllipticK (Real.sin_half_sq_lt_one (abs_lt.2 hθ₀))
  exact continuousAt_const.mul (hK.comp (f := fun θ : ℝ => Real.sin (θ / 2) ^ 2) hp)

/-- The period formula is continuous at zero amplitude, an interior point of `(-π, π)`. -/
lemma continuousAt_periodFormula_zero : ContinuousAt S.periodFormula 0 :=
  S.continuousOn_periodFormula.continuousAt
    (Ioo_mem_nhds (by linarith [Real.pi_pos]) Real.pi_pos)

/-- The period formula tends to the small-angle period as the amplitude tends to zero: it is
  continuous at `0`, where its value is the small-angle period. -/
lemma periodFormula_tendsto_smallAnglePeriod :
    Filter.Tendsto S.periodFormula (nhds 0) (nhds S.smallAnglePeriod) := by
  rw [← S.periodFormula_zero]
  exact S.continuousAt_periodFormula_zero.tendsto

/-!

## B. Monotonicity and bounds in the amplitude

The dependence of the period formula on the amplitude is inherited from the dependence of
`completeEllipticK` on its parameter: on `[0, π)` the parameter `sin² (θ₀/2)` is strictly
increasing in `θ₀` and stays below `1`, and `K` is strictly increasing on `(-∞, 1)`, so the
formula is strictly increasing in the amplitude. The bounds `π/2 ≤ K m ≤ (π/2) (1 - m)^(-1/2)`
on `[0, 1)` sandwich the formula between the small-angle period and
`2π √(ℓ/g) / cos (θ₀/2)`.

-/

/-!

### B.1. Monotonicity in the amplitude

For `0 ≤ θ₁ ≤ θ₂ < π` the half-angles lie in `[0, π/2)`, where the sine is nonnegative and
increasing, so `sin² (θ₁/2) ≤ sin² (θ₂/2) < 1`, and the monotonicity of `K` on its domain does
the rest. The strict version uses the strict monotonicity of the sine on the same interval and
of `K`. Both are restated as bundled `MonotoneOn` and `StrictMonoOn` facts on `[0, π)`.

-/

/-- The period formula is increasing in the amplitude on `[0, π)`: for `0 ≤ θ₁ ≤ θ₂ < π`,
  `periodFormula θ₁ ≤ periodFormula θ₂`. Classically this is the statement that the pendulum is
  not isochronous — the period of libration grows with the amplitude — once `periodFormula` is
  identified with the period (see the TODO). -/
lemma periodFormula_mono {θ₁ θ₂ : ℝ} (h0 : 0 ≤ θ₁) (h12 : θ₁ ≤ θ₂) (hπ : θ₂ < Real.pi) :
    S.periodFormula θ₁ ≤ S.periodFormula θ₂ := by
  have hπ0 := Real.pi_pos
  have hs : Real.sin (θ₁ / 2) ≤ Real.sin (θ₂ / 2) :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) (by linarith)
  have hs0 : 0 ≤ Real.sin (θ₁ / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hm : Real.sin (θ₂ / 2) ^ 2 < 1 := Real.sin_half_sq_lt_one (abs_lt.2 ⟨by linarith, hπ⟩)
  simp only [periodFormula]
  exact mul_le_mul_of_nonneg_left
    (Real.completeEllipticK_mono (pow_le_pow_left₀ hs0 hs 2) hm) (by positivity)

/-- The period formula is strictly increasing in the amplitude on `[0, π)`: for
  `0 ≤ θ₁ < θ₂ < π`, `periodFormula θ₁ < periodFormula θ₂`. -/
lemma periodFormula_strictMono {θ₁ θ₂ : ℝ} (h0 : 0 ≤ θ₁) (h12 : θ₁ < θ₂) (hπ : θ₂ < Real.pi) :
    S.periodFormula θ₁ < S.periodFormula θ₂ := by
  have hπ0 := Real.pi_pos
  have hs : Real.sin (θ₁ / 2) < Real.sin (θ₂ / 2) :=
    Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) (by linarith) (by linarith)
  have hs0 : 0 ≤ Real.sin (θ₁ / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hm : Real.sin (θ₂ / 2) ^ 2 < 1 := Real.sin_half_sq_lt_one (abs_lt.2 ⟨by linarith, hπ⟩)
  have hℓ := S.ℓ_pos
  have hg := S.g_pos
  simp only [periodFormula]
  exact mul_lt_mul_of_pos_left
    (Real.completeEllipticK_strictMono (pow_lt_pow_left₀ hs hs0 two_ne_zero) hm)
    (by positivity)

/-- The period formula is monotone on `[0, π)`, as a bundled `MonotoneOn` statement. -/
lemma monotoneOn_periodFormula : MonotoneOn S.periodFormula (Set.Ico 0 Real.pi) :=
  fun _ h₁ _ h₂ h => S.periodFormula_mono h₁.1 h h₂.2

/-- The period formula is strictly increasing on `[0, π)`, as a bundled `StrictMonoOn`
  statement. -/
lemma strictMonoOn_periodFormula : StrictMonoOn S.periodFormula (Set.Ico 0 Real.pi) :=
  fun _ h₁ _ h₂ h => S.periodFormula_strictMono h₁.1 h h₂.2

/-!

### B.2. Bounds

The lower bound `π/2 ≤ K m` on `[0, 1)` says that the period formula is never below the
small-angle period: the formula is least at zero amplitude, and in particular positive. The
upper bound `K m ≤ (π/2) (1 - m)^(-1/2)`, with `1 - sin² (θ₀/2) = cos² (θ₀/2)`, bounds the
formula by `2π √(ℓ/g) / cos (θ₀/2)` for `|θ₀| < π`: the formula is at most the small-angle
period divided by the cosine of the half-amplitude, a quantity that grows without bound as the
amplitude approaches the inverted position.

-/

/-- The period formula is at least the small-angle period: for `sin² (θ₀/2) < 1`,
  `smallAnglePeriod ≤ periodFormula θ₀`, since `π/2 ≤ K m` on `[0, 1)`. -/
lemma smallAnglePeriod_le_periodFormula {θ₀ : ℝ} (h : Real.sin (θ₀ / 2) ^ 2 < 1) :
    S.smallAnglePeriod ≤ S.periodFormula θ₀ := by
  rw [smallAnglePeriod_eq, periodFormula]
  calc 2 * Real.pi * √(S.ℓ / S.g)
      = 4 * √(S.ℓ / S.g) * (Real.pi / 2) := by ring
    _ ≤ 4 * √(S.ℓ / S.g) * Real.completeEllipticK (Real.sin (θ₀ / 2) ^ 2) :=
        mul_le_mul_of_nonneg_left (Real.pi_div_two_le_completeEllipticK (sq_nonneg _) h)
          (by positivity)

/-- The period formula is positive for `sin² (θ₀/2) < 1`: it is at least the small-angle
  period, which is positive. -/
lemma periodFormula_pos {θ₀ : ℝ} (h : Real.sin (θ₀ / 2) ^ 2 < 1) : 0 < S.periodFormula θ₀ :=
  S.smallAnglePeriod_pos.trans_le (S.smallAnglePeriod_le_periodFormula h)

/-- The period formula is at most `2π √(ℓ/g) / cos (θ₀/2)` for `|θ₀| < π`: the bound
  `K m ≤ (π/2) (1 - m)^(-1/2)` at `m = sin² (θ₀/2)`, where `1 - sin² (θ₀/2) = cos² (θ₀/2)`
  and `cos (θ₀/2) > 0`. -/
lemma periodFormula_le {θ₀ : ℝ} (h : |θ₀| < Real.pi) :
    S.periodFormula θ₀ ≤ 2 * Real.pi * √(S.ℓ / S.g) / Real.cos (θ₀ / 2) := by
  obtain ⟨h₁, h₂⟩ := abs_lt.1 h
  have hc : 0 < Real.cos (θ₀ / 2) := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hpow : (1 - Real.sin (θ₀ / 2) ^ 2) ^ (-(1 / 2 : ℝ)) = (Real.cos (θ₀ / 2))⁻¹ := by
    rw [← Real.cos_sq', ← Real.rpow_two, ← Real.rpow_mul hc.le,
      show (2 : ℝ) * -(1 / 2) = -1 by norm_num, Real.rpow_neg_one]
  rw [periodFormula]
  calc 4 * √(S.ℓ / S.g) * Real.completeEllipticK (Real.sin (θ₀ / 2) ^ 2)
      ≤ 4 * √(S.ℓ / S.g) * (Real.pi / 2 * (1 - Real.sin (θ₀ / 2) ^ 2) ^ (-(1 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left
          (Real.completeEllipticK_le (sq_nonneg _) (Real.sin_half_sq_lt_one h)) (by positivity)
    _ = 2 * Real.pi * √(S.ℓ / S.g) / Real.cos (θ₀ / 2) := by
        rw [hpow]
        ring

/-- The period formula is at most the small-angle period divided by `cos (θ₀/2)`, for
  `|θ₀| < π`: `periodFormula_le` with `2π √(ℓ/g) = smallAnglePeriod`. Together with
  `smallAnglePeriod_le_periodFormula` this sandwiches the formula,
  `smallAnglePeriod ≤ periodFormula θ₀ ≤ smallAnglePeriod / cos (θ₀/2)`; the lower bound holds
  under the more general hypothesis `sin² (θ₀/2) < 1`, which `|θ₀| < π` implies
  (`Real.sin_half_sq_lt_one`). -/
lemma periodFormula_le' {θ₀ : ℝ} (h : |θ₀| < Real.pi) :
    S.periodFormula θ₀ ≤ S.smallAnglePeriod / Real.cos (θ₀ / 2) := by
  rw [smallAnglePeriod_eq]
  exact S.periodFormula_le h

end SimplePendulum

end ClassicalMechanics
