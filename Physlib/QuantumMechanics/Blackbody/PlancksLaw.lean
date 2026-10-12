/-
Copyright (c) 2026 Samyak Rai. All rights reserved.
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
(see `spectralRadianceWave_eq_spectralRadiance`).

## ii. Key results

- `BlackBody` : Structure representing an idealized black body in thermal equilibrium.
- `spectralRadiance` : The spectral radiance per unit frequency of blackbody radiation.
- `spectralRadiance_pos` : The spectral radiance is positive for positive frequency and temperature.
- `spectralRadiance_absZero` : The spectral radiance is 0 at absolute zero.
- `spectralRadianceWave` : Spectral radiance per unit wavelength.
- `spectralRadianceWave_eq_spectralRadiance` : Correspondence between the two forms.
- `firstRadiationConstant` / `secondRadiationConstant` : Radiation constants `c₁L` and `c₂`.
- `spectralRadianceWave_eq_constants` : Planck's law in terms of radiation constants.

## iii. Table of contents

- A. The BlackBody structure
- B. Spectral radiance per unit frequency
- C. Spectral radiance per unit wavelength
- D. Correspondence between the two forms
- E. First and second radiation constants

## iv. References

* https://en.wikipedia.org/wiki/Planck%27s_law
* M. Planck, "Ueber das Gesetz der Energieverteilung im Normalspectrum",
  Ann. Phys. 309 (3), 553–563 (1901).

-/

@[expose] public section

/-!
## A. The BlackBody structure
-/

/-- An idealized black body in thermal equilibrium at temperature `T`. -/
structure BlackBody where
  /-- The temperature of the black body. -/
  T : Temperature

namespace BlackBody

open Constants

/-!
## B. Spectral radiance per unit frequency
-/

/-- The spectral radiance per unit frequency of blackbody radiation at frequency `ν`
    for a black body `B` and speed of light `c`:

    `B(ν, T) = 2 h ν³ / c² · 1 / (e^{h ν / (k_B T)} - 1)`

    By the homogeneity and isotropy of blackbody radiation, the spectral radiance
    is independent of position and direction, so it depends only on frequency
    and temperature.

    Extended by zero outside the physical domain `0 < ν`. -/
noncomputable def spectralRadiance (B : BlackBody) (c : SpeedOfLight) (ν : ℝ) : ℝ :=
  if 0 < ν then
    2 * h * ν ^ 3 / ((c : ℝ) ^ 2 * (Real.exp (h * ν / (kB * (B.T : ℝ))) - 1))
  else 0

/-- The spectral radiance of blackbody radiation is positive for positive frequency
    and positive temperature. -/
lemma spectralRadiance_pos (B : BlackBody) (c : SpeedOfLight) (ν : ℝ)
    (hν : 0 < ν) (hT : 0 < (B.T : ℝ)) : 0 < B.spectralRadiance c ν := by
  rw [spectralRadiance, ite_eq_left hν]
  refine div_pos ?numerator ?denominator
  · exact mul_pos (mul_pos (by norm_num) h_pos) (pow_pos hν 3)
  · have expo_term : 0 < (h : ℝ) * ν / (kB * (B.T : ℝ)) :=
      div_pos (mul_pos h_pos hν) (mul_pos kB_pos hT)
    exact mul_pos (pow_pos c.val_pos 2)
      (sub_pos.mpr (by simpa using Real.exp_strictMono expo_term))

/-- The spectral radiance per unit frequency is non-negative on the physical domain. -/
lemma spectralRadiance_nonneg (B : BlackBody) (c : SpeedOfLight) (ν : ℝ)
    (hν : 0 < ν) (hT : 0 < (B.T : ℝ)) : 0 ≤ B.spectralRadiance c ν :=
  le_of_lt (spectralRadiance_pos B c ν hν hT)

/-- The spectral radiance vanishes at absolute zero temperature. -/
lemma spectralRadiance_absZero (c : SpeedOfLight) (ν : ℝ) :
    spectralRadiance ⟨0⟩ c ν = 0 := by
  unfold spectralRadiance
  split_ifs with hν
  · simp [show ((⟨0⟩ : BlackBody).T : ℝ) = 0 from rfl]
  · rfl

/-- The spectral radiance vanishes at zero frequency. -/
lemma spectralRadiance_zeroFreq (B : BlackBody) (c : SpeedOfLight) :
    B.spectralRadiance c 0 = 0 := by
  rw [spectralRadiance, ite_eq_right (lt_irrefl 0)]

/-- The spectral radiance vanishes when frequency is non-positive. -/
lemma spectralRadiance_eq_zero_of_nonpos_freq (B : BlackBody) (c : SpeedOfLight) (ν : ℝ)
    (hν : ν ≤ 0) : B.spectralRadiance c ν = 0 := by
  rw [spectralRadiance, ite_eq_right (not_lt.mpr hν)]

/-!
## C. Spectral radiance per unit wavelength
-/

/-- Spectral radiance per unit wavelength of blackbody radiation at wavelength
  `λ` for a black body `B` and speed of light `c`:

    `B(λ, T) = 2 h c² / λ⁵ · 1 / (e ^ (h c / (λ kB T)) - 1)`,

  extended by zero outside the physical domain `0 < λ`. -/
noncomputable def spectralRadianceWave (B : BlackBody) (c : SpeedOfLight) (lam : ℝ) : ℝ :=
  if 0 < lam then
    2 * h * (c : ℝ) ^ 2 / lam ^ 5 / (Real.exp (h * (c : ℝ) / (lam * kB * (B.T : ℝ))) - 1)
  else 0

/-- The spectral radiance per unit wavelength is positive for positive wavelength
  and positive temperature. -/
lemma spectralRadianceWave_pos (B : BlackBody) (c : SpeedOfLight) (lam : ℝ)
    (hlam : 0 < lam) (hT : 0 < (B.T : ℝ)) : 0 < B.spectralRadianceWave c lam := by
  unfold spectralRadianceWave
  rw [ite_eq_left hlam]
  have harg : 0 < (h : ℝ) * (c : ℝ) / (lam * kB * (B.T : ℝ)) :=
    div_pos (mul_pos h_pos c.val_pos) (mul_pos (mul_pos hlam kB_pos) hT)
  have h1e : 1 < Real.exp (h * (c : ℝ) / (lam * kB * (B.T : ℝ))) := Real.one_lt_exp_iff.mpr harg
  have hE : 0 < Real.exp (h * (c : ℝ) / (lam * kB * (B.T : ℝ))) - 1 := sub_pos.mpr h1e
  have hnum : 0 < 2 * (h : ℝ) * (c : ℝ) ^ 2 / lam ^ 5 :=
    div_pos (mul_pos (mul_pos zero_lt_two h_pos) (pow_pos c.val_pos 2)) (pow_pos hlam 5)
  exact div_pos hnum hE

/-- The spectral radiance per unit wavelength is non-negative on the physical domain. -/
lemma spectralRadianceWave_nonneg (B : BlackBody) (c : SpeedOfLight) (lam : ℝ)
    (hlam : 0 < lam) (hT : 0 < (B.T : ℝ)) : 0 ≤ B.spectralRadianceWave c lam :=
  le_of_lt (spectralRadianceWave_pos B c lam hlam hT)

/-- The spectral radiance per unit wavelength vanishes at absolute zero. -/
lemma spectralRadianceWave_absZero (c : SpeedOfLight) (lam : ℝ) :
    spectralRadianceWave ⟨0⟩ c lam = 0 := by
  unfold spectralRadianceWave
  split_ifs with hlam
  · simp [show ((⟨0⟩ : BlackBody).T : ℝ) = 0 from rfl]
  · rfl

/-- The spectral radiance per unit wavelength vanishes at zero wavelength. -/
lemma spectralRadianceWave_zeroWave (B : BlackBody) (c : SpeedOfLight) :
    B.spectralRadianceWave c 0 = 0 := by
  unfold spectralRadianceWave
  rw [ite_eq_right (lt_irrefl 0)]

/-- The spectral radiance per unit wavelength vanishes when wavelength is
  non-positive. -/
lemma spectralRadianceWave_eq_zero_of_nonpos_wave (B : BlackBody) (c : SpeedOfLight) (lam : ℝ)
    (hlam : lam ≤ 0) : B.spectralRadianceWave c lam = 0 := by
  unfold spectralRadianceWave
  rw [ite_eq_right (not_lt.mpr hlam)]

/-!
## D. Correspondence between the two forms

Since `B(λ, T) dλ = -B(ν(λ), T) dν` with `ν = c / λ` and `|dν / dλ| = c / λ²`,
the wavelength form equals `c / λ²` times the frequency form evaluated at
`ν = c / λ`.
-/

/-- Correspondence between the wavelength and frequency forms of Planck's law:
  `B(λ, T) = (c / λ²) B(ν = c / λ, T)`. -/
lemma spectralRadianceWave_eq_spectralRadiance (B : BlackBody) (c : SpeedOfLight) (lam : ℝ)
    (hlam : 0 < lam) (hT : 0 < (B.T : ℝ)) :
    B.spectralRadianceWave c lam = ((c : ℝ) / lam ^ 2) * B.spectralRadiance c ((c : ℝ) / lam) := by
  have hclam : 0 < (c : ℝ) / lam := div_pos c.val_pos hlam
  unfold spectralRadianceWave spectralRadiance
  rw [ite_eq_left hlam, ite_eq_left hclam]
  have hexp : (h : ℝ) * ((c : ℝ) / lam) / (kB * (B.T : ℝ)) = h * c / (lam * kB * (B.T : ℝ)) := by
    field_simp
  rw [hexp]
  field_simp

/-!
## E. First and second radiation constants

The wavelength variant uses only the combinations `2 h c²` and `h c / kB`,
called the first and second radiation constants.
-/

/-- The first radiation constant `c₁L = 2 h c²`. -/
noncomputable def firstRadiationConstant (c : SpeedOfLight) : ℝ :=
  2 * h * (c : ℝ) ^ 2

/-- The first radiation constant is positive. -/
lemma firstRadiationConstant_pos (c : SpeedOfLight) :
    0 < firstRadiationConstant c := by
  unfold firstRadiationConstant
  exact mul_pos (mul_pos zero_lt_two h_pos) (pow_pos c.val_pos 2)

/-- The first radiation constant equals `2 * h * c ^ 2`. -/
lemma firstRadiationConstant_eq (c : SpeedOfLight) :
    firstRadiationConstant c = 2 * h * (c : ℝ) ^ 2 := rfl

/-- The second radiation constant `c₂ = h c / kB`. -/
noncomputable def secondRadiationConstant (c : SpeedOfLight) : ℝ :=
  (h : ℝ) * (c : ℝ) / kB

/-- The second radiation constant is positive. -/
lemma secondRadiationConstant_pos (c : SpeedOfLight) :
    0 < secondRadiationConstant c := by
  unfold secondRadiationConstant
  exact div_pos (mul_pos h_pos c.val_pos) kB_pos

/-- The second radiation constant equals `h * c / kB`. -/
lemma secondRadiationConstant_eq (c : SpeedOfLight) :
    secondRadiationConstant c = (h : ℝ) * (c : ℝ) / kB := rfl

/-- Planck's law per unit wavelength in terms of the radiation constants:
  `B(λ, T) = (c₁L / λ⁵) / (e ^ (c₂ / (λ T)) - 1)`. -/
lemma spectralRadianceWave_eq_constants (B : BlackBody) (c : SpeedOfLight) (lam : ℝ)
    (hlam : 0 < lam) (hT : 0 < (B.T : ℝ)) :
    B.spectralRadianceWave c lam
      = firstRadiationConstant c / lam ^ 5
        / (Real.exp (secondRadiationConstant c / (lam * (B.T : ℝ))) - 1) := by
  unfold spectralRadianceWave firstRadiationConstant secondRadiationConstant
  rw [ite_eq_left hlam]
  have hexp : (h : ℝ) * (c : ℝ) / kB / (lam * (B.T : ℝ)) = h * c / (lam * kB * (B.T : ℝ)) := by
    field_simp
  rw [hexp]

end BlackBody
