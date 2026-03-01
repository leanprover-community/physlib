/-
Copyright (c) 2025 Nicola Bernini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicola Bernini
-/
import PhysLean.Meta.Informal.SemiFormal
import PhysLean.ClassicalMechanics.EulerLagrange
import PhysLean.ClassicalMechanics.HamiltonsEquations
/-!

# The Damped Harmonic Oscillator

## i. Overview

The damped harmonic oscillator is a classical mechanical system corresponding to a
mass `m` under a restoring force `- k x` and a damping force `- γ ẋ`, where `k` is the
spring constant, `γ` is the damping coefficient, `x` is the position, and `ẋ` is the velocity.

The equation of motion for the damped harmonic oscillator is:
```
m ẍ + γ ẋ + k x = 0
```

Depending on the relationship between the damping coefficient and the natural frequency,
the system exhibits three different behaviors:
- **Underdamped** (γ² < 4mk) : Oscillatory motion with exponentially decaying amplitude
- **Critically damped** (γ² = 4mk) : Fastest return to equilibrium without oscillation
- **Overdamped** (γ² > 4mk) : Slow return to equilibrium without oscillation

## ii. Key results

This module is currently a placeholder for future implementation. The following results
are planned to be formalized:

- `DampedHarmonicOscillator`: Structure containing the input data (mass, spring constant,
  damping coefficient)
- `EquationOfMotion`: The equation of motion for the damped harmonic oscillator
- Solutions for underdamped, critically damped, and overdamped cases
- Energy dissipation properties
- Quality factor and relaxation time

## iii. Table of contents

- A. The input data (to be implemented)
- B. The damped angular frequency (to be implemented)
- C. The energies and energy dissipation (to be implemented)
- D. The equation of motion (to be implemented)
- E. Solutions (to be implemented)
  - E.1. Underdamped case
  - E.2. Critically damped case
  - E.3. Overdamped case
- F. Quality factor and decay time (to be implemented)

## iv. References

References for the damped harmonic oscillator include:
- Landau & Lifshitz, Mechanics, page 76, section 25.
- Goldstein, Classical Mechanics, Chapter 2.

-/

namespace ClassicalMechanics
open Real
open Space
open InnerProductSpace

TODO "DHO01" "Define the DampedHarmonicOscillator structure with mass m, spring constant k,
  and damping coefficient γ."

TODO "DHO04" "Prove that energy is not conserved and derive the energy dissipation rate."

TODO "DHO05" "Derive solutions for the underdamped case (oscillatory with exponential decay)."

TODO "DHO06" "Derive solutions for the critically damped case (fastest non-oscillatory return)."

TODO "DHO07" "Derive solutions for the overdamped case (slow non-oscillatory return)."

TODO "DHO08" "Define and prove properties of the quality factor Q."

TODO "DHO09" "Define and prove properties of the relaxation time τ."

TODO "DHO10" "Prove that the damped harmonic oscillator reduces to the undamped case when γ = 0."

/-!

## A. The input data (placeholder)

The input data for the damped harmonic oscillator will consist of:
- Mass `m > 0`
- Spring constant `k > 0`
- Damping coefficient `γ ≥ 0`

-/

/-- Placeholder structure for the damped harmonic oscillator.
  The damped harmonic oscillator is specified by a mass `m`, a spring constant `k`,
  and a damping coefficient `γ`. All parameters are assumed to be positive (or non-negative
  for the damping coefficient). -/
structure DampedHarmonicOscillator where
  /-- The mass of the oscillator. -/
  m : ℝ
  /-- The spring constant of the oscillator. -/
  k : ℝ
  /-- The damping coefficient of the oscillator. -/
  γ : ℝ
  m_pos : 0 < m
  k_pos : 0 < k
  γ_nonneg : 0 ≤ γ

namespace DampedHarmonicOscillator

variable (S : DampedHarmonicOscillator)

@[simp]
lemma k_ne_zero : S.k ≠ 0 := Ne.symm (ne_of_lt S.k_pos)

@[simp]
lemma m_ne_zero : S.m ≠ 0 := Ne.symm (ne_of_lt S.m_pos)

/-!

## B. The natural angular frequency (placeholder)

The natural angular frequency ω₀ = √(k/m) will be defined here.

-/

/-- The natural (undamped) angular frequency of the oscillator, ω₀ = √(k/m). -/
noncomputable def ω₀ : ℝ := √(S.k / S.m)

@[simp]
lemma ω₀_pos : 0 < S.ω₀ := sqrt_pos.mpr (div_pos S.k_pos S.m_pos)

lemma ω₀_sq : S.ω₀^2 = S.k / S.m := by
  rw [ω₀, sq_sqrt]
  exact div_nonneg (le_of_lt S.k_pos) (le_of_lt S.m_pos)

/-!
## C. Equation of motion (Tag: DHO03)

The damped harmonic oscillator with mass `m`, spring
constant `k`, and damping coefficient `γ` satisfies

    m ẍ + γ ẋ + k x = 0,

where `x : Time → ℝ` is the position as a function of time.
-/

/-- The equation of motion for the damped harmonic oscillator.

A function `x : Time → ℝ` is a solution if it satisfies

    S.m * x¨ + S.γ * ẋ + S.k * x = 0

for all times `t`. -/
noncomputable def EquationOfMotion (x : Time → ℝ) : Prop :=
  ∀ t : Time,
    S.m * (Time.deriv (Time.deriv x) t) +
    S.γ * (Time.deriv x t) +
    S.k * x t = 0

/-!
## D. The energies and energy dissipation (Tag: DHO04)

For the damped harmonic oscillator, the mechanical energy is

  E(t) = ½ S.m (ẋ(t))^2 + ½ S.k (x(t))^2,

where `x : Time → ℝ` is the position as a function of time.

If `x` satisfies the equation of motion

  S.m * x¨ + S.γ * ẋ + S.k * x = 0,

then differentiating `E` with respect to time and substituting the
equation of motion yields

  dE/dt = - S.γ * (ẋ(t))^2 ≤ 0

Thus the energy is non-increasing in time, and it is strictly decreasing
whenever `S.γ > 0` and `ẋ(t) ≠ 0`. In particular, for `S.γ > 0`
the energy is not conserved, and the energy dissipation rate is
proportional to the squared velocity.
-/

/-- The kinetic energy of the damped harmonic oscillator. -/
noncomputable def kineticEnergy (x : Time → ℝ) : Time → ℝ :=
  fun t => (1 / 2 : ℝ) * S.m * (Time.deriv x t)^2

/-- The potential energy of the damped harmonic oscillator. -/
noncomputable def potentialEnergy (x : Time → ℝ) : Time → ℝ :=
  fun t => (1 / 2 : ℝ) * S.k * (x t)^2

/-- Mechanical energy of the damped harmonic oscillator. -/
noncomputable def energy (x : Time → ℝ) : Time → ℝ :=
  S.kineticEnergy x + S.potentialEnergy x

/-- Energy dissipation rate along a trajectory `x : Time → ℝ`.

  if `x` satisfies `S.equationOfMotion x`, then

  Time.deriv (S.energy x) t = - S.γ * (Time.deriv x t)^2,

so the energy is non-increasing and not conserved when `S.γ > 0`. -/
noncomputable def energyDissipationRate (x : Time → ℝ) : Time → ℝ :=
  fun t => - S.γ * (Time.deriv x t)^2

/-!

## E. Damping regimes (placeholder)

The three damping regimes will be defined based on the discriminant γ² - 4mk.

-/

/-- The discriminant that determines the damping regime. -/
noncomputable def discriminant : ℝ := S.γ^2 - 4 * S.m * S.k

/-- The system is underdamped when γ² < 4mk. -/
def IsUnderdamped : Prop := S.discriminant < 0

/-- The system is critically damped when γ² = 4mk. -/
def IsCriticallyDamped : Prop := S.discriminant = 0

/-- The system is overdamped when γ² > 4mk. -/
def IsOverdamped : Prop := S.discriminant > 0

end DampedHarmonicOscillator

end ClassicalMechanics
