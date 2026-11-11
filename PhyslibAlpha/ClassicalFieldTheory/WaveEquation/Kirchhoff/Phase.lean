/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.WaveEquation.Kirchhoff.Setting

/-!
# Fourier properties of wave propagation

The spectral description uses the Fourier phase and the sine multiplier of the wave propagator.

## i. Overview

The spectral description uses the Fourier phase and the sine multiplier of the wave propagator.

## ii. Key results

* `phase`: The Fourier phase as a complex exponential.
* `phase_add`.
* `norm_phase`.
* `phase_eq_fourierChar` : the phase is the Fourier character.
* `IsWavePropagator`: Fourier multiplier, finite propagation speed and Huygens' principle.

## iii. Table of contents

- A. Fourier properties of wave propagation

## iv. References

* Bär, [Green-hyperbolic operators on globally hyperbolic
  spacetimes](https://arxiv.org/abs/1310.0738).

## A. Fourier properties of wave propagation
-/

@[expose] public section

noncomputable section

namespace WaveEquation.Kirchhoff

open MeasureTheory Complex
open scoped FourierTransform SchwartzMap

/-- The Fourier phase as a complex exponential. -/
noncomputable def phase (t : ℝ) : ℂ := Complex.exp (-(2 * Real.pi * Complex.I * t))

lemma phase_add (s t : ℝ) : phase (s + t) = phase s * phase t := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma norm_phase (t : ℝ) : ‖phase t‖ = 1 := by
  unfold phase
  rw [Complex.norm_exp]
  simp

lemma continuous_phase : Continuous phase := by
  unfold phase
  fun_prop

/-- The phase is the Fourier character at `-u`. -/
lemma phase_eq_fourierChar (u : ℝ) : phase u = (𝐞 (-u) : ℂ) := by
  rw [Real.fourierChar_apply]
  unfold phase
  push_cast
  ring_nf

/-- An operator on scalar fields on `ℝ³`. -/
abbrev WaveOperator := (Space 3 → ℂ) → (Space 3 → ℂ)

/-- The operator acts on Schwartz functions as the Fourier multiplier `sin(ω t) / ω` with
`ω = 2π c |ξ|`. Frequencies `ξ = 0` are excluded. There the multiplier has the limit `t`. -/
def HasWaveFourierMultiplier (c t : ℝ) (T : WaveOperator) : Prop :=
  ∀ (f : 𝓢(Space 3, ℂ)) (ξ : Space 3), ξ ≠ 0 →
    ∫ x : Space 3, phase (inner ℝ x ξ) * T f x =
      ((Real.sin (2 * Real.pi * c * ‖ξ‖ * t) / (2 * Real.pi * c * ‖ξ‖) : ℝ) : ℂ) *
        ∫ x : Space 3, phase (inner ℝ x ξ) * f x

/-- Finite propagation speed for `c > 0`: if `f` vanishes outside the ball of radius `ρ` about `x₀`,
then `T f` vanishes outside the ball of radius `ρ + c |t|`. -/
def HasFinitePropagationSpeed (c t : ℝ) (T : WaveOperator) : Prop :=
  ∀ (f : Space 3 → ℂ) (x₀ : Space 3) (ρ : ℝ), (∀ y, ρ < ‖y - x₀‖ → f y = 0) →
    ∀ x, ρ + c * |t| < ‖x - x₀‖ → T f x = 0

/-- Huygens' principle for `c > 0`: if `f` vanishes outside the ball of radius `ρ` about `x₀`, then
`T f` vanishes inside the ball of radius `c |t| - ρ`. The wavefront is a shell of width `2ρ`
with no wave behind it. -/
def SatisfiesHuygensPrinciple (c t : ℝ) (T : WaveOperator) : Prop :=
  ∀ (f : Space 3 → ℂ) (x₀ : Space 3) (ρ : ℝ), (∀ y, ρ < ‖y - x₀‖ → f y = 0) →
    ∀ x, ‖x - x₀‖ + ρ < c * |t| → T f x = 0

/-- The three properties of the free wave propagator in three dimensions: the Fourier multiplier,
finite propagation speed and Huygens' principle. This is a bundle of properties of one operator and
not a characterisation of wave propagators. -/
structure IsWavePropagator (c t : ℝ) (T : WaveOperator) : Prop where
  /-- The Fourier multiplier is `sin(ω t) / ω`. -/
  multiplier : HasWaveFourierMultiplier c t T
  /-- Signals travel at most at speed `c`. -/
  finiteSpeed : HasFinitePropagationSpeed c t T
  /-- The wave vanishes behind the wavefront. -/
  huygens : SatisfiesHuygensPrinciple c t T

end WaveEquation.Kirchhoff
