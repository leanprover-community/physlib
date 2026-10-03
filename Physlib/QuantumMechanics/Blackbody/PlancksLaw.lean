/-
Copyright (c) 2026 Samyak Rai, Dwanith C. Jayanth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samyak Rai, Dwanith C. Jayanth
-/
module

public import Physlib.Thermodynamics.Temperature.Basic
public import Physlib.Relativity.SpeedOfLight
public import Physlib.QuantumMechanics.PlanckConstant
public import Mathlib.Analysis.SpecialFunctions.Exponential

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

and per unit wavelength `λ`, given by

    `B(λ, T) = 2 h c² / λ⁵ · 1 / (e^{h c / (λ k_B T)} - 1)`

The two forms are related by `B(λ, T) = (c / λ²) B(ν = c/λ, T)`
(see `spectralRadianceWave_eq_freq`).

## ii. Key results

- `spectralRadiance` : The spectral radiance per unit frequency of blackbody radiation.
- `spectralRadiance_pos` : The spectral radiance is positive for positive frequency
  and temperature.
- `spectralRadiance_absZero` : The spectral radiance is 0 at absolute zero.
- `spectralRadianceFreq` : Parametrized spectral radiance per unit frequency.
- `spectralRadianceWave` : Parametrized spectral radiance per unit wavelength.
- `spectralRadianceWave_eq_freq` : Correspondence between the two forms.
- `firstRadiationConstant` / `secondRadiationConstant` : Radiation constants `c₁L` and `c₂`.
- `spectralRadianceWave_eq_constants` : Planck's law in terms of radiation constants.

## iii. Table of contents

- A. The spectral radiance
- B. Parametrized spectral radiance per unit frequency
- C. Spectral radiance per unit wavelength
- D. Correspondence between the two forms
- E. First and second radiation constants

## iv. References

* https://en.wikipedia.org/wiki/Planck%27s_law
* M. Planck, "Ueber das Gesetz der Energieverteilung im Normalspectrum",
  Ann. Phys. 309 (3), 553–563 (1901).

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

/-!
## B. Parametrized spectral radiance per unit frequency
-/

/-- Spectral radiance per unit frequency of blackbody radiation at frequency `ν`
  and temperature `T`:

    `B(ν, T) = 2 h ν³ / c² · 1 / (e ^ (h ν / (kB T)) - 1)`,

  extended by zero outside the physical domain. -/
noncomputable def spectralRadianceFreq (h c kB ν T : ℝ) : ℝ :=
  if 0 < ν ∧ 0 < T then
    2 * h * ν ^ 3 / (c ^ 2 * (Real.exp (h * ν / (kB * T)) - 1))
  else 0

/-- Correspondence between `spectralRadiance` and `spectralRadianceFreq`. -/
lemma spectralRadiance_eq_spectralRadianceFreq (c : SpeedOfLight) (ν : ℝ) (T : Temperature) :
    spectralRadiance c ν T = spectralRadianceFreq h (c : ℝ) kB ν (T : ℝ) := rfl

/-- The spectral radiance per unit frequency is positive for positive frequency
  and positive temperature. -/
lemma spectralRadianceFreq_pos (h c kB ν T : ℝ) (hh : 0 < h) (hc : 0 < c)
    (hk : 0 < kB) (hν : 0 < ν) (hT : 0 < T) :
    0 < spectralRadianceFreq h c kB ν T := by
  unfold spectralRadianceFreq
  rw [if_pos ⟨hν, hT⟩]
  apply div_pos
  · exact mul_pos (mul_pos zero_lt_two hh) (pow_pos hν 3)
  · apply mul_pos (pow_pos hc 2)
    have harg : 0 < h * ν / (kB * T) :=
      div_pos (mul_pos hh hν) (mul_pos hk hT)
    have h1e : 1 < Real.exp (h * ν / (kB * T)) := Real.one_lt_exp_iff.mpr harg
    linarith

/-- The spectral radiance per unit frequency vanishes at absolute zero. -/
@[simp]
lemma spectralRadianceFreq_absZero (h c kB ν : ℝ) :
    spectralRadianceFreq h c kB ν 0 = 0 := by
  unfold spectralRadianceFreq
  simp

/-- The spectral radiance per unit frequency vanishes at zero frequency. -/
@[simp]
lemma spectralRadianceFreq_zeroFreq (h c kB T : ℝ) :
    spectralRadianceFreq h c kB 0 T = 0 := by
  unfold spectralRadianceFreq
  simp

/-!
## C. Spectral radiance per unit wavelength
-/

/-- Spectral radiance per unit wavelength of blackbody radiation at wavelength
  `λ` and temperature `T`:

    `B(λ, T) = 2 h c² / λ⁵ · 1 / (e ^ (h c / (λ kB T)) - 1)`,

  extended by zero outside the physical domain. -/
noncomputable def spectralRadianceWave (h c kB lam T : ℝ) : ℝ :=
  if 0 < lam ∧ 0 < T then
    2 * h * c ^ 2 / lam ^ 5 / (Real.exp (h * c / (lam * kB * T)) - 1)
  else 0

/-- The spectral radiance per unit wavelength is positive for positive wavelength
  and positive temperature. -/
lemma spectralRadianceWave_pos (h c kB lam T : ℝ) (hh : 0 < h) (hc : 0 < c)
    (hk : 0 < kB) (hlam : 0 < lam) (hT : 0 < T) :
    0 < spectralRadianceWave h c kB lam T := by
  unfold spectralRadianceWave
  rw [if_pos ⟨hlam, hT⟩]
  have harg : 0 < h * c / (lam * kB * T) :=
    div_pos (mul_pos hh hc) (mul_pos (mul_pos hlam hk) hT)
  have h1e : 1 < Real.exp (h * c / (lam * kB * T)) := Real.one_lt_exp_iff.mpr harg
  have hE : 0 < Real.exp (h * c / (lam * kB * T)) - 1 := sub_pos.mpr h1e
  have hnum : 0 < 2 * h * c ^ 2 / lam ^ 5 :=
    div_pos (mul_pos (mul_pos zero_lt_two hh) (pow_pos hc 2)) (pow_pos hlam 5)
  exact div_pos hnum hE

/-- The spectral radiance per unit wavelength vanishes at absolute zero. -/
@[simp]
lemma spectralRadianceWave_absZero (h c kB lam : ℝ) :
    spectralRadianceWave h c kB lam 0 = 0 := by
  unfold spectralRadianceWave
  simp

/-- The spectral radiance per unit wavelength vanishes at zero wavelength. -/
@[simp]
lemma spectralRadianceWave_zeroWave (h c kB T : ℝ) :
    spectralRadianceWave h c kB 0 T = 0 := by
  unfold spectralRadianceWave
  simp

/-!
## D. Correspondence between the two forms

Since `B(λ, T) dλ = -B(ν(λ), T) dν` with `ν = c / λ` and `|dν / dλ| = c / λ²`,
the wavelength form equals `c / λ²` times the frequency form evaluated at
`ν = c / λ`.
-/

/-- Correspondence between the wavelength and frequency forms of Planck's law:
  `B(λ, T) = (c / λ²) B(ν = c / λ, T)`. -/
lemma spectralRadianceWave_eq_freq (h c kB lam T : ℝ) (hh : 0 < h) (hc : 0 < c)
    (hk : 0 < kB) (hlam : 0 < lam) (hT : 0 < T) :
    spectralRadianceWave h c kB lam T
      = (c / lam ^ 2) * spectralRadianceFreq h c kB (c / lam) T := by
  have h1 : 0 < lam ∧ 0 < T := ⟨hlam, hT⟩
  have h2 : 0 < c / lam ∧ 0 < T := ⟨div_pos hc hlam, hT⟩
  unfold spectralRadianceWave spectralRadianceFreq
  rw [if_pos h1, if_pos h2]
  have hlam' : lam ≠ 0 := ne_of_gt hlam
  have hc' : c ≠ 0 := ne_of_gt hc
  have hkT : kB * T ≠ 0 := mul_ne_zero (ne_of_gt hk) (ne_of_gt hT)
  have hE : Real.exp (h * c / (lam * kB * T)) - 1 ≠ 0 := by
    have harg : 0 < h * c / (lam * kB * T) :=
      div_pos (mul_pos hh hc) (mul_pos (mul_pos hlam hk) hT)
    have h1e : 1 < Real.exp (h * c / (lam * kB * T)) := Real.one_lt_exp_iff.mpr harg
    exact ne_of_gt (sub_pos.mpr h1e)
  have hexp : h * (c / lam) / (kB * T) = h * c / (lam * kB * T) := by
    field_simp
  rw [hexp]
  field_simp

/-!
## E. First and second radiation constants

The wavelength variant uses only the combinations `2 h c²` and `h c / kB`,
called the first and second radiation constants.
-/

/-- The first radiation constant `c₁L = 2 h c²`. -/
noncomputable def firstRadiationConstant (h c : ℝ) : ℝ := 2 * h * c ^ 2

/-- The second radiation constant `c₂ = h c / kB`. -/
noncomputable def secondRadiationConstant (h c kB : ℝ) : ℝ := h * c / kB

/-- The first radiation constant is positive. -/
lemma firstRadiationConstant_pos (h c : ℝ) (hh : 0 < h) (hc : 0 < c) :
    0 < firstRadiationConstant h c := by
  unfold firstRadiationConstant
  exact mul_pos (mul_pos zero_lt_two hh) (pow_pos hc 2)

/-- The second radiation constant is positive. -/
lemma secondRadiationConstant_pos (h c kB : ℝ) (hh : 0 < h) (hc : 0 < c)
    (hk : 0 < kB) :
    0 < secondRadiationConstant h c kB := by
  unfold secondRadiationConstant
  exact div_pos (mul_pos hh hc) hk

/-- Planck's law per unit wavelength in terms of the radiation constants:
  `B(λ, T) = (c₁L / λ⁵) / (e ^ (c₂ / (λ T)) - 1)`. -/
lemma spectralRadianceWave_eq_constants (h c kB lam T : ℝ) (hh : 0 < h)
    (hc : 0 < c) (hk : 0 < kB) (hlam : 0 < lam) (hT : 0 < T) :
    spectralRadianceWave h c kB lam T
      = firstRadiationConstant h c / lam ^ 5
        / (Real.exp (secondRadiationConstant h c kB / (lam * T)) - 1) := by
  have h1 : 0 < lam ∧ 0 < T := ⟨hlam, hT⟩
  unfold spectralRadianceWave firstRadiationConstant secondRadiationConstant
  rw [if_pos h1]
  have hlam' : lam ≠ 0 := ne_of_gt hlam
  have hk' : kB ≠ 0 := ne_of_gt hk
  have hT' : T ≠ 0 := ne_of_gt hT
  have hE : Real.exp (h * c / (lam * kB * T)) - 1 ≠ 0 := by
    have harg : 0 < h * c / (lam * kB * T) :=
      div_pos (mul_pos hh hc) (mul_pos (mul_pos hlam hk) hT)
    have h1e : 1 < Real.exp (h * c / (lam * kB * T)) := Real.one_lt_exp_iff.mpr harg
    exact ne_of_gt (sub_pos.mpr h1e)
  have hexp : h * c / kB / (lam * T) = h * c / (lam * kB * T) := by
    field_simp
  rw [hexp]

/-- The spectral radiance per unit frequency is non-negative on the physical domain. -/
lemma spectralRadianceFreq_nonneg (h c kB ν T : ℝ) (hh : 0 < h) (hc : 0 < c)
    (hk : 0 < kB) (hν : 0 < ν) (hT : 0 < T) :
    0 ≤ spectralRadianceFreq h c kB ν T :=
  le_of_lt (spectralRadianceFreq_pos h c kB ν T hh hc hk hν hT)

/-- The spectral radiance per unit wavelength is non-negative on the physical domain. -/
lemma spectralRadianceWave_nonneg (h c kB lam T : ℝ) (hh : 0 < h) (hc : 0 < c)
    (hk : 0 < kB) (hlam : 0 < lam) (hT : 0 < T) :
    0 ≤ spectralRadianceWave h c kB lam T :=
  le_of_lt (spectralRadianceWave_pos h c kB lam T hh hc hk hlam hT)

/-- The spectral radiance per unit frequency vanishes when frequency is
  non-positive (the if-guard `0 < ν ∧ 0 < T` fails). -/
lemma spectralRadianceFreq_eq_zero_of_nonpos_freq (h c kB ν T : ℝ) (hν : ν ≤ 0) :
    spectralRadianceFreq h c kB ν T = 0 := by
  unfold spectralRadianceFreq
  rw [if_neg (not_and_of_not_left _ (not_lt.mpr hν))]

/-- The spectral radiance per unit wavelength vanishes when wavelength is
  non-positive (the if-guard `0 < lam ∧ 0 < T` fails). -/
lemma spectralRadianceWave_eq_zero_of_nonpos_wave (h c kB lam T : ℝ) (hlam : lam ≤ 0) :
    spectralRadianceWave h c kB lam T = 0 := by
  unfold spectralRadianceWave
  rw [if_neg (not_and_of_not_left _ (not_lt.mpr hlam))]

/-- The first radiation constant equals `2 * h * c ^ 2`. -/
@[simp]
lemma firstRadiationConstant_eq (h c : ℝ) :
    firstRadiationConstant h c = 2 * h * c ^ 2 := rfl

/-- The second radiation constant equals `h * c / kB`. -/
@[simp]
lemma secondRadiationConstant_eq (h c kB : ℝ) :
    secondRadiationConstant h c kB = h * c / kB := rfl

end Blackbody
