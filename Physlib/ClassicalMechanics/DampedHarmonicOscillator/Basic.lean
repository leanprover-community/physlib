/-
Copyright (c) 2026 Nicola Bernini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicola Bernini, Florian Wiesner
-/
module

public import Physlib.ClassicalMechanics.HarmonicOscillator.Basic
/-!

# The damped harmonic oscillator

## i. Overview

The damped harmonic oscillator is a classical mechanical system consisting of a mass `m`
under a restoring force `- k x` and a damping force `- γ ẋ`, where `k` is the spring
constant, `γ` is the damping coefficient, `x` is the position, and `ẋ` is the velocity.

The equation of motion for the damped harmonic oscillator is:
```
m ẍ + γ ẋ + k x = 0
```

Depending on the relationship between the damping coefficient and the natural frequency,
the system exhibits three different behaviors:
- **Underdamped** (`γ^2 < 4 * m * k`) : oscillatory motion with exponentially decaying
  amplitude.
- **Critically damped** (`γ^2 = 4 * m * k`) : fastest return to equilibrium without
  oscillation.
- **Overdamped** (`4 * m * k < γ^2`) : slow return to equilibrium without oscillation.

In this file, the position and velocity both have type `EuclideanSpace ℝ (Fin 1)`. This
coordinate model is useful for a first formalization, but it works only because the
one-dimensional configuration space and its tangent space are both isomorphic to
one-dimensional Euclidean space. A more geometric formalization should represent the
configuration space and its tangent bundle directly.

## ii. Key results

The key results in the study of the classical damped harmonic oscillator are the following:

In the `Basic` module:
- `DampedHarmonicOscillator` contains the input data to the problem.
- `EquationOfMotion` defines the damped oscillator equation `m ẍ + γ ẋ + k x = 0`.
- `energy_dissipation_rate` computes the rate at which damping removes mechanical energy.
- `IsUnderdamped`, `IsCriticallyDamped`, and `IsOverdamped` define the three damping
  regimes from the discriminant `γ^2 - 4 * m * k`.
- `angularFrequency` selects the real frequency parameter from the damping regime.
- `qualityFactor` and `relaxationTime` define the quality factor `Q = ω / (2 β)` and the
  amplitude relaxation time `τ = 1 / β` from the decay rate `β = γ / (2 m)`;
  `isUnderdamped_iff_qualityFactor` and its companions characterise the three damping
  regimes by `Q`.
- `toUndamped_equationOfMotion` relates the damped and undamped equations of motion when
  the damping coefficient is zero.
- `lagrangian` defines the Caldirola–Kanai lagrangian `exp (γ/m * t) * (T - V)`.
- `gradLagrangian` defines the variational gradient of the corresponding action, and
  `equationOfMotion_iff_gradLagrangian_zero` shows that its vanishing is equivalent to
  the equation of motion.

In the `Solution` module:
- `InitialConditions` contains the initial position and velocity.
- `trajectory` gives the explicit solution selected from the damping regime.

## iii. Table of contents

- A. The input data
- B. The equation of motion and energy dissipation
  - B.1. The equation of motion
  - B.2. Energy dissipation
- C. Newton's second law
  - C.1. The force
  - C.2. Equation of motion if and only if Newton's second law
- D. Damping regimes
  - D.1. The discriminant, the decay rate and the angular frequency
  - D.2. The quality factor and the relaxation time
- E. To undamped oscillator
- F. The Caldirola–Kanai lagrangian and the equation of motion
  - F.1. The lagrangian
    - F.1.1. Equalities for the lagrangian
    - F.1.2. Smoothness of the lagrangian
    - F.1.3. Gradients of the lagrangian
  - F.2. The variational gradient of the action
    - F.2.1. The variational gradient and Newton's second law
  - F.3. Equation of motion iff the variational gradient vanishes

## iv. References

References for the damped harmonic oscillator include:

* Landau & Lifshitz, Mechanics, page 76, section 25. [ref: landau_mechanics]
* Goldstein, Classical Mechanics, Chapter 6, Section 6.5 (Forced Vibrations and the Effect of
  Dissipative Forces). [ref: goldstein_classicalmechanics]

References for the Caldirola–Kanai lagrangian include:

* Caldirola, Nuovo Cimento 18 (1941) 393. [ref: caldirola_1941]
* Kanai, Progress of Theoretical Physics 3 (1948) 440. [ref: kanai_1948]
-/

@[expose] public section

namespace ClassicalMechanics
open Real
open Space
open InnerProductSpace
open MeasureTheory
open ContDiff
open Time

TODO "Create a new file for the geometric model which properly models the
  position as a configuration space and velocity as its tangent space, see the
  HarmonicOscillator file."

/-!

## A. The input data

We start by defining a structure containing the input data of the damped harmonic oscillator.
The mass `m` and spring constant `k` are inherited from `HarmonicOscillator`; this file adds
the damping coefficient `γ`.

-/

/-- The classical damped harmonic oscillator is specified by a mass `m`, a spring
constant `k`, and a damping coefficient `γ`.

The mass and spring constant are inherited from `HarmonicOscillator` and are positive.
The damping coefficient is assumed to be nonnegative. -/
@[ext]
structure DampedHarmonicOscillator extends HarmonicOscillator where
  /-- The damping coefficient of the oscillator. -/
  γ : ℝ
  /-- The damping coefficient is nonnegative. -/
  γ_nonneg : 0 ≤ γ

namespace DampedHarmonicOscillator

variable (S : DampedHarmonicOscillator)

/-!
The mass/spring nonzero lemmas, the natural angular frequency, and the undamped energy API
are inherited from `HarmonicOscillator`.
-/

/-!

## B. The equation of motion and energy dissipation

### B.1. The equation of motion

-/

/-- The equation of motion for the damped harmonic oscillator:
`m ẍ + γ ẋ + k x = 0`. -/
noncomputable def EquationOfMotion (xₜ : Time → EuclideanSpace ℝ (Fin 1)) : Prop :=
  ∀ t : Time, S.m • ∂ₜ (∂ₜ xₜ) t + S.γ • ∂ₜ xₜ t + S.k • xₜ t = 0

/-- Solving the equation of motion for the acceleration: along a solution the second derivative
is `-(k/m) x - (γ/m) ẋ`. -/
lemma acceleration_eq_of_equationOfMotion (z : Time → EuclideanSpace ℝ (Fin 1))
    (hEOM : S.EquationOfMotion z) (t : Time) :
    ∂ₜ (∂ₜ z) t = (-(S.m⁻¹ * S.k)) • z t + (-(S.m⁻¹ * S.γ)) • ∂ₜ z t := by
  have hm : S.m ≠ 0 := S.m_ne_zero
  have hsum : S.m • ∂ₜ (∂ₜ z) t + (S.γ • ∂ₜ z t + S.k • z t) = 0 := by
    rw [← add_assoc]; exact hEOM t
  have hma : S.m • ∂ₜ (∂ₜ z) t = -(S.k • z t) - S.γ • ∂ₜ z t := by
    rw [eq_neg_of_add_eq_zero_left hsum]; module
  have hkey : ∂ₜ (∂ₜ z) t = S.m⁻¹ • (S.m • ∂ₜ (∂ₜ z) t) := by
    rw [smul_smul, inv_mul_cancel₀ hm, one_smul]
  rw [hkey, hma]
  module

/-!

### B.2. Energy dissipation

The damped oscillator inherits the mechanical energy from the undamped harmonic oscillator.
Along a solution of the damped equation of motion, that energy decreases at a rate
proportional to `-γ ‖ẋ‖^2`.

-/

/-- Along a smooth solution of the damped equation of motion, the derivative of the
mechanical energy is `-γ ‖ẋ‖^2`. -/
lemma energy_dissipation_rate (xₜ : Time → EuclideanSpace ℝ (Fin 1)) (t : Time)
    (h1 : S.EquationOfMotion xₜ)
    (hx : ContDiff ℝ ∞ xₜ) :
    ∂ₜ (S.energy xₜ) t = - S.γ * ⟪∂ₜ xₜ t, ∂ₜ xₜ t⟫_ℝ := by
  rw [S.energy_deriv xₜ hx]
  have hforce : S.m • ∂ₜ (∂ₜ xₜ) t + S.k • xₜ t = - S.γ • ∂ₜ xₜ t := by
    linear_combination (norm := module) h1 t
  simp [hforce, inner_smul_right]

/-- If `0 < γ` and the velocity is nonzero at a time, the mechanical energy is strictly
decreasing at that time. -/
lemma energy_not_conserved (xₜ : Time → EuclideanSpace ℝ (Fin 1)) (t : Time)
    (h1 : S.EquationOfMotion xₜ) (hx : ContDiff ℝ ∞ xₜ) (hdx : ∂ₜ xₜ t ≠ 0) (hγ : 0 < S.γ) :
    ∂ₜ (S.energy xₜ) t < 0 := by
  rw [energy_dissipation_rate S xₜ t h1 hx, neg_mul]
  exact neg_neg_of_pos (mul_pos hγ (real_inner_self_pos.mpr hdx))

/-!
## C. Newton's second law

We define the force of the damped oscillator, and show that the equation of
motion is equivalent to Newton's second law.

-/

/-!

### C.1. The force

We define the force of the damped oscillator as `- k x - γ v`.

-/

/-- The force of the damped harmonic oscillator at a given position and time. -/
noncomputable def force (S : DampedHarmonicOscillator)
    (xₜ : Time → EuclideanSpace ℝ (Fin 1)) (t : Time) :
    EuclideanSpace ℝ (Fin 1) := - S.k • xₜ t - S.γ • ∂ₜ xₜ t

/-!

### C.2. Equation of motion if and only if Newton's second law

We show that the equation of motion is equivalent to Newton's second law.

-/

lemma equationOfMotion_iff_newtons_2nd_law (xₜ : Time → EuclideanSpace ℝ (Fin 1)) :
    S.EquationOfMotion xₜ ↔
    (∀ t : Time, S.m • ∂ₜ (∂ₜ xₜ) t = force S xₜ t) := by
  simp only [EquationOfMotion, force]
  constructor
  · intro h t
    linear_combination (norm := module) h t
  · intro h t
    linear_combination (norm := module) h t

/-!
## D. Damping regimes

The sign of the discriminant `γ^2 - 4 * m * k` separates the underdamped, critically
damped, and overdamped regimes. We also define the decay rate and the regime-selected
real frequency that appears in the explicit solution formulas.

-/

/-!

### D.1. The discriminant, the decay rate and the angular frequency

-/

/-- The discriminant that determines the damping regime. -/
noncomputable def discriminant : ℝ := S.γ^2 - 4 * S.m * S.k

/-- The exponential decay rate `γ / (2 * m)`. -/
noncomputable def decayRate : ℝ := S.γ / (2 * S.m)

/-- The system is underdamped when γ² < 4mk. -/
def IsUnderdamped : Prop := S.discriminant < 0

/-- The system is critically damped when γ² = 4mk. -/
def IsCriticallyDamped : Prop := S.discriminant = 0

/-- The system is overdamped when 4mk < γ². -/
def IsOverdamped : Prop := 0 < S.discriminant

/-- Every damped oscillator is underdamped, critically damped, or overdamped. -/
lemma isUnderdamped_or_isCriticallyDamped_or_isOverdamped :
    S.IsUnderdamped ∨ S.IsCriticallyDamped ∨ S.IsOverdamped :=
  lt_trichotomy S.discriminant 0

/-- The system is undamped when γ = 0. -/
def IsUndamped : Prop := S.γ = 0

/-- The real frequency selected by the damping regime.

In the underdamped regime this is the oscillation frequency. In the critically damped
regime it is `0`. In the overdamped regime this is the real split rate between the two
roots. -/
noncomputable def angularFrequency : ℝ := by
  classical
  exact
    if S.IsUnderdamped then
      sqrt (- S.discriminant) / (2 * S.m)
    else if S.IsCriticallyDamped then
      0
    else
      sqrt S.discriminant / (2 * S.m)

/-- The relationship between the discriminant, decay rate, and natural angular frequency. -/
lemma discriminant_eq_four_mul_m_sq_mul_decayRate_sq_sub_ω_sq :
    S.discriminant = 4 * S.m^2 * (S.decayRate^2 - S.ω^2) := by
  rw [discriminant, decayRate, S.ω_sq]
  field_simp [S.m_ne_zero]
  ring

/-- The decay rate is nonnegative. -/
lemma decayRate_nonneg : 0 ≤ S.decayRate := by
  exact div_nonneg S.γ_nonneg (by nlinarith [S.m_pos])

/-- The decay rate is positive when the damping coefficient is positive. -/
lemma decayRate_pos (hγ : 0 < S.γ) : 0 < S.decayRate :=
  div_pos hγ (by linarith [S.m_pos])

/-- An undamped oscillator lies in the underdamped regime. -/
lemma isUnderdamped_of_gamma_eq_zero (hγ : S.γ = 0) : S.IsUnderdamped := by
  rw [IsUnderdamped, discriminant, hγ]
  nlinarith [mul_pos S.m_pos S.k_pos]

/-- An underdamped system has decay rate less than the natural frequency. -/
lemma isUnderdamped_decayRate (hS : S.IsUnderdamped) : S.decayRate < S.ω := by
  rw [IsUnderdamped, discriminant_eq_four_mul_m_sq_mul_decayRate_sq_sub_ω_sq] at hS
  have hsq : S.decayRate ^ 2 < S.ω ^ 2 := by nlinarith [sq_pos_of_pos S.m_pos]
  nlinarith [S.decayRate_nonneg, S.ω_pos]

/-- A critically damped system has decay rate equal to the natural frequency. -/
lemma isCriticallyDamped_decayRate (hS : S.IsCriticallyDamped) : S.ω = S.decayRate := by
  rw [IsCriticallyDamped, discriminant_eq_four_mul_m_sq_mul_decayRate_sq_sub_ω_sq] at hS
  have hsq : S.decayRate ^ 2 = S.ω ^ 2 := by nlinarith [sq_pos_of_pos S.m_pos]
  nlinarith [S.decayRate_nonneg, S.ω_pos]

/-- The damping coefficient is twice mass times the decay rate. -/
lemma gamma_eq_two_mul_m_mul_decayRate : S.γ = 2 * S.m * S.decayRate := by
  rw [decayRate]
  field_simp [S.m_ne_zero]

/-- The spring constant is `m * ω^2`. -/
lemma k_eq_m_mul_ω_sq : S.k = S.m * S.ω^2 := by
  rw [S.ω_sq]
  field_simp [S.m_ne_zero]

/-- In the critically damped regime, `k = m * decayRate^2`. -/
lemma k_eq_m_mul_decayRate_sq_of_criticallyDamped (hS : S.IsCriticallyDamped) :
    S.k = S.m * S.decayRate^2 := by
  rw [S.k_eq_m_mul_ω_sq, S.isCriticallyDamped_decayRate hS]

/-- An overdamped system has decay rate greater than the natural frequency. -/
lemma isOverdamped_decayRate (hS : S.IsOverdamped) : S.ω < S.decayRate := by
  rw [IsOverdamped, discriminant_eq_four_mul_m_sq_mul_decayRate_sq_sub_ω_sq] at hS
  have hsq : S.ω ^ 2 < S.decayRate ^ 2 := by nlinarith [sq_pos_of_pos S.m_pos]
  nlinarith [S.decayRate_nonneg, S.ω_pos]

/-- In the underdamped regime, the selected frequency uses the oscillation frequency. -/
lemma angularFrequency_eq_underdamped (hS : S.IsUnderdamped) :
    S.angularFrequency = sqrt (- S.discriminant) / (2 * S.m) := by
  simp [angularFrequency, hS]

/-- In the critically damped regime, the selected frequency is zero. -/
lemma angularFrequency_eq_criticallyDamped (hS : S.IsCriticallyDamped) :
    S.angularFrequency = 0 := by
  rw [IsCriticallyDamped] at hS
  simp [angularFrequency, IsUnderdamped, IsCriticallyDamped, hS]

/-- In the overdamped regime, the selected frequency uses the real split rate. -/
lemma angularFrequency_eq_overdamped (hS : S.IsOverdamped) :
    S.angularFrequency = sqrt S.discriminant / (2 * S.m) := by
  rw [IsOverdamped] at hS
  simp [angularFrequency, IsUnderdamped, IsCriticallyDamped, not_lt.mpr hS.le, hS.ne']

/-- In the underdamped regime, the selected angular frequency squares to
`ω^2 - decayRate^2`. -/
lemma angularFrequency_sq_of_underdamped (hS : S.IsUnderdamped) :
    S.angularFrequency^2 = S.ω^2 - S.decayRate^2 := by
  rw [S.angularFrequency_eq_underdamped hS, div_pow, sq_sqrt]
  · rw [discriminant_eq_four_mul_m_sq_mul_decayRate_sq_sub_ω_sq]
    field_simp [S.m_ne_zero]
    ring
  · exact (neg_pos.mpr hS).le

/-- The selected angular frequency is positive in the underdamped regime. -/
lemma angularFrequency_pos_of_underdamped (hS : S.IsUnderdamped) :
    0 < S.angularFrequency := by
  rw [S.angularFrequency_eq_underdamped hS]
  exact div_pos (sqrt_pos.mpr (neg_pos.mpr hS)) (by linarith [S.m_pos])

/-- The selected angular frequency is nonzero in the underdamped regime. -/
lemma angularFrequency_ne_zero_of_underdamped (hS : S.IsUnderdamped) :
    S.angularFrequency ≠ 0 :=
  (S.angularFrequency_pos_of_underdamped hS).ne'

/-- In the overdamped regime, the selected angular frequency squares to
`decayRate^2 - ω^2`. -/
lemma angularFrequency_sq_of_overdamped (hS : S.IsOverdamped) :
    S.angularFrequency^2 = S.decayRate^2 - S.ω^2 := by
  rw [S.angularFrequency_eq_overdamped hS, div_pow, sq_sqrt]
  · rw [discriminant_eq_four_mul_m_sq_mul_decayRate_sq_sub_ω_sq]
    field_simp [S.m_ne_zero]
    ring
  · exact le_of_lt hS

/-- The selected angular frequency is positive in the overdamped regime. -/
lemma angularFrequency_pos_of_overdamped (hS : S.IsOverdamped) :
    0 < S.angularFrequency := by
  rw [S.angularFrequency_eq_overdamped hS]
  exact div_pos (sqrt_pos.mpr hS) (by linarith [S.m_pos])

/-- The selected angular frequency is nonzero in the overdamped regime. -/
lemma angularFrequency_ne_zero_of_overdamped (hS : S.IsOverdamped) :
    S.angularFrequency ≠ 0 :=
  (S.angularFrequency_pos_of_overdamped hS).ne'

/-- The underdamped regime is characterised by `β < ω`. -/
lemma isUnderdamped_iff_decayRate_lt : S.IsUnderdamped ↔ S.decayRate < S.ω := by
  refine ⟨S.isUnderdamped_decayRate, fun h => ?_⟩
  rcases S.isUnderdamped_or_isCriticallyDamped_or_isOverdamped with hS | hS | hS
  · exact hS
  · exact absurd (S.isCriticallyDamped_decayRate hS) h.ne'
  · exact absurd (S.isOverdamped_decayRate hS) (lt_asymm h)

/-- The critically damped regime is characterised by `ω = β`. -/
lemma isCriticallyDamped_iff_eq_decayRate : S.IsCriticallyDamped ↔ S.ω = S.decayRate := by
  refine ⟨S.isCriticallyDamped_decayRate, fun h => ?_⟩
  rcases S.isUnderdamped_or_isCriticallyDamped_or_isOverdamped with hS | hS | hS
  · exact absurd (S.isUnderdamped_decayRate hS) (by rw [h]; exact lt_irrefl _)
  · exact hS
  · exact absurd (S.isOverdamped_decayRate hS) (by rw [h]; exact lt_irrefl _)

/-- The overdamped regime is characterised by `ω < β`. -/
lemma isOverdamped_iff_lt_decayRate : S.IsOverdamped ↔ S.ω < S.decayRate := by
  refine ⟨S.isOverdamped_decayRate, fun h => ?_⟩
  rcases S.isUnderdamped_or_isCriticallyDamped_or_isOverdamped with hS | hS | hS
  · exact absurd (S.isUnderdamped_decayRate hS) (lt_asymm h)
  · exact absurd (S.isCriticallyDamped_decayRate hS) h.ne
  · exact hS

/-!

### D.2. The quality factor and the relaxation time

The quality factor `Q = ω / (2 β)` and the amplitude relaxation time `τ = 1 / β` are the
usual dimensionless and dimensionful measures of the damping, both expressed through the
decay rate `β = γ / (2 m)`. When `γ = 0` both are `0` by the convention `x / 0 = 0` of Lean,
so the lemmas below assume `0 < γ` whenever the value matters.

-/

/-- The quality factor `Q = ω / (2 β)`, equal to `m ω / γ` and to `√(m k) / γ`: the ratio of
the natural angular frequency to the width `γ / m` of the resonance.

When `γ = 0` the value is `0` by the convention `x / 0 = 0`. -/
noncomputable def qualityFactor : ℝ := S.ω / (2 * S.decayRate)

/-- The relaxation time `τ = 1 / β` of the amplitude, equal to `2 m / γ`; the exponential
factor of the solutions is `exp (-t / τ)` (see `exp_neg_decayRate_mul`).

When `γ = 0` the value is `0` by the convention `0⁻¹ = 0`. -/
noncomputable def relaxationTime : ℝ := S.decayRate⁻¹

/-- The quality factor equals `m ω / γ`. -/
lemma qualityFactor_eq_m_mul_ω_div : S.qualityFactor = S.m * S.ω / S.γ := by
  unfold qualityFactor decayRate
  field_simp [S.m_ne_zero]

/-- The quality factor equals `√(m k) / γ`. -/
lemma qualityFactor_eq_sqrt_div : S.qualityFactor = √(S.m * S.k) / S.γ := by
  rw [S.qualityFactor_eq_m_mul_ω_div, S.k_eq_m_mul_ω_sq,
    show S.m * (S.m * S.ω ^ 2) = (S.m * S.ω) ^ 2 by ring,
    Real.sqrt_sq (mul_nonneg S.m_pos.le S.ω_pos.le)]

/-- The quality factor is positive when the damping coefficient is positive. -/
lemma qualityFactor_pos (hγ : 0 < S.γ) : 0 < S.qualityFactor := by
  rw [S.qualityFactor_eq_m_mul_ω_div]
  exact div_pos (mul_pos S.m_pos S.ω_pos) hγ

/-- The square of the quality factor equals `m k / γ ^ 2`. -/
lemma qualityFactor_sq : S.qualityFactor ^ 2 = S.m * S.k / S.γ ^ 2 := by
  rw [S.qualityFactor_eq_sqrt_div, div_pow, Real.sq_sqrt (mul_nonneg S.m_pos.le S.k_pos.le)]

/-- The discriminant in terms of the quality factor: `γ ^ 2 - 4 m k = 4 m k (1 / (4 Q ^ 2) - 1)`;
for `γ = 0` both sides equal `-4 m k`. -/
lemma discriminant_eq_qualityFactor :
    S.discriminant = 4 * S.m * S.k * (1 / (4 * S.qualityFactor ^ 2) - 1) := by
  rw [S.qualityFactor_sq, discriminant]
  rcases eq_or_ne S.γ 0 with h | h
  · simp [h]
  · field_simp [h, S.m_ne_zero, S.k_ne_zero]

/-- The underdamped regime is characterised by `1 / 2 < Q` when `0 < γ`. -/
lemma isUnderdamped_iff_qualityFactor (hγ : 0 < S.γ) :
    S.IsUnderdamped ↔ 1 / 2 < S.qualityFactor := by
  have hβ := S.decayRate_pos hγ
  rw [S.isUnderdamped_iff_decayRate_lt, qualityFactor, lt_div_iff₀ (by linarith)]
  constructor <;> intro h <;> linarith

/-- The critically damped regime is characterised by `Q = 1 / 2` when `0 < γ`. -/
lemma isCriticallyDamped_iff_qualityFactor (hγ : 0 < S.γ) :
    S.IsCriticallyDamped ↔ S.qualityFactor = 1 / 2 := by
  have hβ := S.decayRate_pos hγ
  rw [S.isCriticallyDamped_iff_eq_decayRate, qualityFactor, div_eq_iff (by linarith)]
  constructor <;> intro h <;> linarith

/-- The overdamped regime is characterised by `Q < 1 / 2` when `0 < γ`. -/
lemma isOverdamped_iff_qualityFactor (hγ : 0 < S.γ) :
    S.IsOverdamped ↔ S.qualityFactor < 1 / 2 := by
  have hβ := S.decayRate_pos hγ
  rw [S.isOverdamped_iff_lt_decayRate, qualityFactor, div_lt_iff₀ (by linarith)]
  constructor <;> intro h <;> linarith

/-- In the underdamped regime the selected angular frequency satisfies
`ω_d ^ 2 = ω ^ 2 (1 - 1 / (4 Q ^ 2))` when `0 < γ`. -/
lemma angularFrequency_sq_eq_qualityFactor (hγ : 0 < S.γ) (hS : S.IsUnderdamped) :
    S.angularFrequency ^ 2 = S.ω ^ 2 * (1 - 1 / (4 * S.qualityFactor ^ 2)) := by
  have hβ := (S.decayRate_pos hγ).ne'
  rw [S.angularFrequency_sq_of_underdamped hS, qualityFactor]
  field_simp [S.ω_ne_zero, hβ]
  ring

/-- The relaxation time equals `2 m / γ`. -/
lemma relaxationTime_eq : S.relaxationTime = 2 * S.m / S.γ := by
  rw [relaxationTime, decayRate, inv_div]

/-- The decay rate and the relaxation time are inverse to each other when `0 < γ`. -/
lemma decayRate_mul_relaxationTime (hγ : 0 < S.γ) : S.decayRate * S.relaxationTime = 1 :=
  mul_inv_cancel₀ (S.decayRate_pos hγ).ne'

/-- The relaxation time is positive when the damping coefficient is positive. -/
lemma relaxationTime_pos (hγ : 0 < S.γ) : 0 < S.relaxationTime :=
  inv_pos.mpr (S.decayRate_pos hγ)

/-- The quality factor equals `ω τ / 2`; this holds for `γ = 0` as well, both sides being `0`. -/
lemma qualityFactor_eq_ω_mul_relaxationTime : S.qualityFactor = S.ω * S.relaxationTime / 2 := by
  rw [qualityFactor, relaxationTime]
  ring

/-- The exponential factor `exp (-β t)` of the solutions equals `exp (-t / τ)`; for `γ = 0`
both sides equal `1`. -/
lemma exp_neg_decayRate_mul (t : Time) :
    exp (-S.decayRate * t) = exp (-(t : ℝ) / S.relaxationTime) := by
  rw [relaxationTime, div_inv_eq_mul]
  ring_nf

/-!
## E. To undamped oscillator

We show that the damped harmonic oscillator reduces to the undamped harmonic oscillator when the
damping coefficient is zero. The underlying mass and spring data are already inherited from
`HarmonicOscillator`; the proof argument records that this conversion is being used only in
the zero-damping case.

We also show that the equations of motion are equivalent in this case.
-/

set_option linter.unusedVariables false in
/-- Convert a damped oscillator to its underlying undamped oscillator when `γ = 0`. -/
@[nolint unusedArguments]
def toUndamped (S : DampedHarmonicOscillator) (_hS : S.IsUndamped) :
    HarmonicOscillator :=
  S.toHarmonicOscillator

/-- When `γ = 0`, the damped equation of motion is equivalent to the equation of motion
for the corresponding undamped harmonic oscillator. -/
lemma toUndamped_equationOfMotion (S : DampedHarmonicOscillator) (hS : S.IsUndamped)
    (xₜ : Time → EuclideanSpace ℝ (Fin 1)) (hx : ContDiff ℝ ∞ xₜ) :
    S.EquationOfMotion xₜ ↔ (S.toUndamped hS).EquationOfMotion xₜ := by
  have hγ : S.γ = 0 := by simpa [IsUndamped] using hS
  rw [S.equationOfMotion_iff_newtons_2nd_law xₜ,
    (S.toUndamped hS).equationOfMotion_iff_newtons_2nd_law xₜ hx]
  refine forall_congr' fun t => ?_
  rw [show (S.toUndamped hS).m = S.m from rfl,
    show HarmonicOscillator.force (S.toUndamped hS) (xₜ t) = force S xₜ t from by
      simp [force, HarmonicOscillator.force_eq_linear, toUndamped, hγ]]

/-!

## F. The Caldirola–Kanai lagrangian and the equation of motion

The damped harmonic oscillator is not conservative, so the undamped lagrangian
`T - V` does not reproduce the damped equation of motion. Instead we use the
Caldirola–Kanai lagrangian, which multiplies the undamped lagrangian by the
time-dependent factor `exp (γ/m * t)`:

$$L(t, x, v) = e^{(\gamma/m) t}\left(\frac{1}{2} m \|v\|^2 - \frac{1}{2} k \|x\|^2\right)$$

Setting the variational gradient of the corresponding action equal to zero
recovers exactly the damped equation of motion `m ẍ + γ ẋ + k x = 0`.

-/

/-!

### F.1. The lagrangian

We define the Caldirola–Kanai lagrangian as the lagrangian of the underlying
undamped harmonic oscillator multiplied by the exponential factor `exp (γ/m * t)`.

-/

/-- The Caldirola–Kanai lagrangian of the damped harmonic oscillator. It is the
lagrangian of the underlying undamped harmonic oscillator multiplied by the
time-dependent factor `exp (γ/m * t)`. -/
noncomputable def lagrangian (t : Time) (x v : EuclideanSpace ℝ (Fin 1)) : ℝ :=
  exp (S.γ / S.m * t) * S.toHarmonicOscillator.lagrangian t x v

/-!

#### F.1.1. Equalities for the lagrangian

We prove some simple equalities for the lagrangian, in particular that when applied to a
trajectory it is the exponential factor times the kinetic energy minus the potential energy,
and that it reduces to the undamped lagrangian when the damping coefficient is zero.

-/

lemma lagrangian_eq : S.lagrangian = fun (t : Time) (x v : EuclideanSpace ℝ (Fin 1)) =>
    exp (S.γ / S.m * t) * (1 / (2 : ℝ) * S.m * ⟪v, v⟫_ℝ - 1 / (2 : ℝ) * S.k * ⟪x, x⟫_ℝ) := by
  funext t x v
  rw [lagrangian, S.toHarmonicOscillator.lagrangian_eq]

lemma lagrangian_eq_exp_mul_kineticEnergy_sub_potentialEnergy (t : Time)
    (xₜ : Time → EuclideanSpace ℝ (Fin 1)) :
    S.lagrangian t (xₜ t) (∂ₜ xₜ t) =
      exp (S.γ / S.m * t) * (S.kineticEnergy xₜ t - S.potentialEnergy (xₜ t)) := by
  rw [lagrangian, S.toHarmonicOscillator.lagrangian_eq_kineticEnergy_sub_potentialEnergy]

/-- When the damping coefficient is zero, the Caldirola–Kanai lagrangian is the
lagrangian of the underlying undamped harmonic oscillator. -/
lemma lagrangian_of_isUndamped (hS : S.IsUndamped) :
    S.lagrangian = S.toHarmonicOscillator.lagrangian := by
  have hγ : S.γ = 0 := by simpa [IsUndamped] using hS
  funext t x v
  simp [lagrangian, hγ]

/-!

#### F.1.2. Smoothness of the lagrangian

The lagrangian is smooth in all its arguments.

-/

@[fun_prop]
lemma contDiff_lagrangian (n : WithTop ℕ∞) : ContDiff ℝ n ↿S.lagrangian := by
  show ContDiff ℝ n fun p : Time × EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1) =>
    exp (S.γ / S.m * p.1) * ↿S.toHarmonicOscillator.lagrangian p
  fun_prop

/-!

#### F.1.3. Gradients of the lagrangian

We now show results related to the gradients of the lagrangian with respect to the
position and velocity. They follow from the corresponding gradients of the undamped
lagrangian, using that the gradient scales with the constant `exp (γ/m * t)`.

-/

lemma gradient_lagrangian_position_eq (t : Time) (x v : EuclideanSpace ℝ (Fin 1)) :
    gradient (fun x => S.lagrangian t x v) x = -(exp (S.γ / S.m * t) * S.k) • x := by
  have hf : DifferentiableAt ℝ (fun y => S.toHarmonicOscillator.lagrangian t y v) x := by
    simp only [HarmonicOscillator.lagrangian_eq]
    fun_prop
  rw [show (fun y => S.lagrangian t y v) =
      fun y => exp (S.γ / S.m * t) * S.toHarmonicOscillator.lagrangian t y v from rfl,
    gradient_const_mul _ hf, S.toHarmonicOscillator.gradient_lagrangian_position_eq]
  module

lemma gradient_lagrangian_velocity_eq (t : Time) (x v : EuclideanSpace ℝ (Fin 1)) :
    gradient (S.lagrangian t x) v = (exp (S.γ / S.m * t) * S.m) • v := by
  have hf : DifferentiableAt ℝ (fun w => S.toHarmonicOscillator.lagrangian t x w) v := by
    simp only [HarmonicOscillator.lagrangian_eq]
    fun_prop
  rw [show S.lagrangian t x =
      fun w => exp (S.γ / S.m * t) * S.toHarmonicOscillator.lagrangian t x w from rfl,
    gradient_const_mul _ hf, S.toHarmonicOscillator.gradient_lagrangian_velocity_eq, smul_smul]

/-!

### F.2. The variational gradient of the action

We now write down the variational gradient of the action of the damped harmonic
oscillator, for a trajectory $x(t)$ this is equal to

$$t\mapsto \left.\frac{\partial L(t, q, \dot x (t))}{\partial q}\right|_{q = x(t)} -
  \frac{d}{dt} \left.\frac{\partial L(t, x(t), v)}{\partial v}\right|_{v = \dot x (t)}$$

Setting this equal to zero corresponds to the Euler-Lagrange equations, and thereby the
equation of motion.

-/

/-- The variational gradient of the action of the damped harmonic oscillator. -/
noncomputable def gradLagrangian (xₜ : Time → EuclideanSpace ℝ (Fin 1)) :
    Time → EuclideanSpace ℝ (Fin 1) :=
  (δ (q':=xₜ), ∫ t, S.lagrangian t (q' t) (fderiv ℝ q' t 1))

lemma gradLagrangian_eq_eulerLagrangeOp (xₜ : Time → EuclideanSpace ℝ (Fin 1))
    (hq : ContDiff ℝ ∞ xₜ) :
    S.gradLagrangian xₜ = eulerLagrangeOp S.lagrangian xₜ := by
  rw [gradLagrangian,
    ClassicalMechanics.euler_lagrange_varGradient _ _ hq (S.contDiff_lagrangian _)]

/-!

#### F.2.1. The variational gradient and Newton's second law

We simplify the variational gradient of the action to the exponential factor times
the difference between the force and mass times acceleration.

-/

private lemma deriv_exp_smul (a : ℝ) (y : Time → EuclideanSpace ℝ (Fin 1))
    (hy : Differentiable ℝ y) (t : Time) :
    ∂ₜ (fun t' : Time => exp (a * t'.val) • y t') t =
      exp (a * t.val) • (∂ₜ y t + a • y t) := by
  rw [Time.deriv, fderiv_fun_smul (by fun_prop) (hy t), fderiv_exp (by fun_prop),
    fderiv_fun_mul (by fun_prop) (by fun_prop)]
  simp only [_root_.add_apply, _root_.smul_apply,
    ContinuousLinearMap.smulRight_apply, Time.fderiv_val, smul_eq_mul, mul_one]
  rw [← Time.deriv_eq]
  simp [smul_add, smul_smul]

/-- The variational gradient of the Caldirola–Kanai action is the exponential factor
times the difference of the force and mass times acceleration appearing in
Newton's second law. -/
lemma gradLagrangian_eq_force (xₜ : Time → EuclideanSpace ℝ (Fin 1)) (hx : ContDiff ℝ ∞ xₜ) :
    S.gradLagrangian xₜ = fun t : Time =>
      exp (S.γ / S.m * t) • (force S xₜ t - S.m • ∂ₜ (∂ₜ xₜ) t) := by
  have hdx : Differentiable ℝ (∂ₜ xₜ) := deriv_differentiable_of_contDiff xₜ hx
  funext t
  rw [gradLagrangian_eq_eulerLagrangeOp S xₜ hx, eulerLagrangeOp]
  have h2 : ∂ₜ (fun t' => gradient (S.lagrangian t' (xₜ t') ·) (∂ₜ xₜ t')) t =
      exp (S.γ / S.m * t) • (S.m • ∂ₜ (∂ₜ xₜ) t + S.γ • ∂ₜ xₜ t) := by
    conv_lhs =>
      arg 1
      ext t'
      rw [gradient_lagrangian_velocity_eq, ← smul_smul]
    rw [deriv_exp_smul (S.γ / S.m) (fun t' => S.m • ∂ₜ xₜ t') (hdx.const_smul S.m) t,
      Time.deriv_smul _ _ hdx, smul_smul, div_mul_cancel₀ _ S.m_ne_zero]
  rw [gradient_lagrangian_position_eq, h2, force]
  module

/-!

### F.3. Equation of motion iff the variational gradient vanishes

The equation of motion of the damped harmonic oscillator holds if and only if the
variational gradient of the Caldirola–Kanai action vanishes, since the exponential
factor is never zero.

-/

lemma equationOfMotion_iff_gradLagrangian_zero (xₜ : Time → EuclideanSpace ℝ (Fin 1))
    (hx : ContDiff ℝ ∞ xₜ) :
    S.EquationOfMotion xₜ ↔ S.gradLagrangian xₜ = 0 := by
  rw [S.equationOfMotion_iff_newtons_2nd_law xₜ, gradLagrangian_eq_force S xₜ hx, funext_iff]
  refine forall_congr' fun t => ?_
  simp only [Pi.zero_apply, smul_eq_zero, Real.exp_ne_zero, false_or, sub_eq_zero]
  exact eq_comm

end DampedHarmonicOscillator

end ClassicalMechanics
