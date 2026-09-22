/-
Copyright (c) 2026 Samyak Rai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samyak Rai
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Physlib.Meta.Informal.Basic
public import Physlib.Thermodynamics.Temperature.Basic
public import Physlib.StatisticalMechanics.BoltzmannConstant
public import Physlib.Relativity.SpeedOfLight
public import Physlib.QuantumMechanics.PlanckConstant

/-!

# Planck's Law

In this module we define Planck's law for blackbody radiation: The spectral density of
electromagnetic radiation emitted by a black body in thermal equilibrium at a given
temperature T, when there is no net flow of matter or energy between the body and
its environment.

## i. Overview

According to Planck's distribution law, the spectral energy radiance
(per unit frequency) for a black body at given temperature `T` as a function of frequency `ν`
 is given by

    `B(ν, T) = 2 h ν³ / c² · 1 / (e^{h ν / (k_B T)} - 1)`

where `h` is Planck's constant, `c` the speed of light, and `k_B` the Boltzmann constant.

## ii. Key results

- `spectralRadiance` : The spectral radiance per unit frequency of blackbody radiation.
- `spectralRadiance_pos` : The spectral radiance is positive for positive frequency
  and temperature.
- `spectralRadiance_absZero` : The spectral radiance is 0 at absolute zero.

## iii. Table of contents

- A. The spectral radiance

## iv. References

* https://en.wikipedia.org/wiki/Planck%27s_law

-/

@[expose] public section


namespace Blackbody

/-!
## A. The spectral radiance
-/

open Constants

/-- The spectral radiance per unit frequency of blackbody radiation at frequency `ν`
    and temperature `T`, for a system of units in which the speed of light is `c`:

    `B(ν, T) = 2 h ν³ / c² · 1 / (e^{h ν / (k_B T)} - 1)`

    By the homogeneity and isotropy of blackbody radiation, the spectral radiance
    is independent of position and direction, so it depends only on frequency
    and temperature.

    Extended by zero outside the physical domain; zero is the unique continuous
    extension since the Rayleigh–Jeans limit vanishes -/
noncomputable def spectralRadiance (c : SpeedOfLight) (ν : ℝ) (T : Temperature) : ℝ :=
    if 0 < ν ∧ 0 < (T : ℝ) then
      2 * h * ν ^ 3 / ((c : ℝ) ^ 2 * (Real.exp (h * ν / (kB * (T : ℝ))) - 1))
    else 0

/-- The spectral radiance of blackbody radiation is positive for positive frequency
    and positive temperature. -/
lemma spectralRadiance_pos (c : SpeedOfLight) (ν : ℝ) (T : Temperature)
    (ν_pos : 0 < ν) (T_pos : 0 < T.val) : 0 < spectralRadiance c ν T := by
    have if_cond : 0 < ν ∧ 0 < (T : ℝ) := ⟨ν_pos, by exact_mod_cast T_pos⟩
    rw [spectralRadiance, ite_eq_left if_cond]
    refine div_pos ?numerator ?denominator
    · exact mul_pos (mul_pos (by norm_num) h_pos) (pow_pos ν_pos 3)
    · have expo_term : 0 < h * ν / (kB * (T : ℝ)) :=
        div_pos (mul_pos h_pos ν_pos) (mul_pos kB_pos (by exact_mod_cast T_pos))
      exact mul_pos (pow_pos c.val_pos 2)
       (sub_pos.mpr (by simpa using Real.exp_strictMono expo_term))

/-- Explicit promise for Spectral Radiance vanishing at absolute zero Temperature. -/
lemma spectralRadiance_absZero (c : SpeedOfLight) (ν : ℝ) :
    spectralRadiance c ν ⟨0⟩ = 0 := by
    rw [spectralRadiance, ite_eq_right]
    rintro ⟨ν_pos, T_zero⟩
    exact lt_irrefl _ T_zero

end Blackbody
