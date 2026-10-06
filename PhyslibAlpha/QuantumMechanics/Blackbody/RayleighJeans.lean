/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import Mathlib.MeasureTheory.Integral.Gamma
public import Physlib.QuantumMechanics.Blackbody.PlancksLaw
public import Physlib.StatisticalMechanics.CanonicalEnsemble.Lemmas
/-!

# Planck's law lies strictly below the Rayleigh–Jeans law

## i. Overview

A field mode of frequency `ν` in thermal equilibrium at temperature `T` is an oscillator.
Treated as a canonical ensemble with continuous energies `E ≥ 0`, its mean energy is `kB T`
(equipartition) and the spectral radiance is the Rayleigh–Jeans law `2 ν² kB T / c²`.
Treated as a canonical ensemble with quantized energies `n h ν`, its mean energy is
`h ν / (e^{h ν / (kB T)} - 1)` and the spectral radiance is Planck's law. Since `e^x - 1 > x`
for `x > 0`, the quantized mean energy is strictly below `kB T` at every frequency and every
positive temperature: no continuous Boltzmann statistics reproduces Planck's law. This is the
starting point of Poincaré's 1911–1912 proof that the quantum is necessary.

## ii. Key results

- `quantizedOscillator` : the canonical ensemble of levels `n ε`, `n : ℕ`.
- `quantizedOscillator_meanEnergy` : its mean energy is `ε / (e^{β ε} - 1)`.
- `classicalOscillator` : the canonical ensemble of energies `E > 0` with Lebesgue measure.
- `classicalOscillator_meanEnergy` : its mean energy is `kB T`.
- `quantizedOscillator_meanEnergy_lt` : the quantized mean energy is below `kB T`.
- `spectralRadiance_eq_meanEnergy` : Planck's law is `2 ν² / c²` times the quantized mean energy.
- `rayleighJeans` : the Rayleigh–Jeans spectral radiance `2 ν² kB T / c²`.
- `spectralRadiance_lt_rayleighJeans` : Planck's law is strictly below Rayleigh–Jeans.

## iii. Table of contents

- A. The quantized oscillator
- B. The classical oscillator
- C. Planck's law and the Rayleigh–Jeans law

## iv. References

* H. Poincaré, *Sur la théorie des quanta*, J. Phys. Théor. Appl. 2 (1912) 5–34.
* https://en.wikipedia.org/wiki/Rayleigh%E2%80%93Jeans_law

-/

@[expose] public section

namespace BlackBody

open MeasureTheory Real Constants Temperature CanonicalEnsemble

/-!

## A. The quantized oscillator

-/

/-- The quantized oscillator with level spacing `ε`: the microstates `n : ℕ` have energy `n ε`
and are counted with unit weight. -/
noncomputable def quantizedOscillator (ε : ℝ) : CanonicalEnsemble ℕ where
  energy n := n * ε
  dof := 0
  energy_measurable := measurable_from_nat
  μ := Measure.count

/-- For `x > 0`, the Boltzmann factor `e^{-x}` has norm below one. -/
lemma exp_neg_lt_one {x : ℝ} (hx : 0 < x) : ‖exp (-x)‖ < 1 := by
  rw [norm_of_nonneg (exp_pos _).le]
  exact exp_lt_one_iff.mpr (neg_lt_zero.mpr hx)

/-- The Boltzmann factor of the level `n` is the `n`-th power of that of the first level. -/
lemma exp_neg_mul_nat (b ε : ℝ) (n : ℕ) : exp (-b * (n * ε)) = exp (-(b * ε)) ^ n := by
  rw [← exp_nat_mul]
  ring_nf

/-- The partition sum of the levels: `∑ e^{-β n ε} = (1 - e^{-β ε})⁻¹`. -/
lemma hasSum_exp_neg_levels {b ε : ℝ} (hb : 0 < b * ε) :
    HasSum (fun n : ℕ => exp (-b * (n * ε))) (1 - exp (-(b * ε)))⁻¹ := by
  simpa only [exp_neg_mul_nat] using hasSum_geometric_of_norm_lt_one (exp_neg_lt_one hb)

/-- The energy sum of the levels: `∑ n ε e^{-β n ε} = ε e^{-β ε} / (1 - e^{-β ε})²`. -/
lemma hasSum_energy_levels {b ε : ℝ} (hb : 0 < b * ε) :
    HasSum (fun n : ℕ => n * ε * exp (-b * (n * ε)))
      (ε * (exp (-(b * ε)) / (1 - exp (-(b * ε))) ^ 2)) := by
  convert (hasSum_coe_mul_geometric_of_norm_lt_one (exp_neg_lt_one hb)).mul_left ε using 2
  rw [exp_neg_mul_nat]
  ring

/-- The mean energy of the quantized oscillator is Planck's `ε / (e^{β ε} - 1)`. -/
lemma quantizedOscillator_meanEnergy {ε : ℝ} (hε : 0 < ε) {T : Temperature}
    (hT : 0 < (T : ℝ)) :
    (quantizedOscillator ε).meanEnergy T = ε / (exp (T.β * ε) - 1) := by
  have hb : 0 < (T.β : ℝ) * ε := by
    rw [β_toReal]
    exact mul_pos (one_div_pos.mpr (mul_pos kB_pos hT)) hε
  have hZ := hasSum_exp_neg_levels hb
  have hU := hasSum_energy_levels hb
  have hint {f : ℕ → ℝ} {a : ℝ} (hf : HasSum f a) (hf0 : ∀ n, 0 ≤ f n) :
      ∫ n, f n ∂Measure.count = a := by
    rw [integral_countable (integrable_count_iff.mpr
      (hf.summable.congr fun n => (norm_of_nonneg (hf0 n)).symm))]
    simpa using hf.tsum_eq
  rw [meanEnergy_eq_ratio_of_integrals]
  change (∫ n : ℕ, (n : ℝ) * ε * exp (-T.β * (n * ε)) ∂Measure.count) /
    (∫ n : ℕ, exp (-T.β * ((n : ℝ) * ε)) ∂Measure.count) = _
  rw [hint hU fun n => by positivity, hint hZ fun n => (exp_pos _).le]
  have h1 : 1 - exp (-(T.β * ε)) ≠ 0 := by
    have := exp_lt_one_iff.mpr (neg_lt_zero.mpr hb)
    linarith
  have h2 : exp (T.β * ε) - 1 ≠ 0 := (sub_pos.mpr (one_lt_exp_iff.mpr hb)).ne'
  rw [exp_neg] at h1 ⊢
  field_simp

/-!

## B. The classical oscillator

-/

/-- The classical oscillator: energies `E > 0` with Lebesgue measure. -/
noncomputable def classicalOscillator : CanonicalEnsemble ℝ where
  energy E := E
  dof := 0
  energy_measurable := measurable_id
  μ := volume.restrict (Set.Ioi 0)

/-- Equipartition: the mean energy of the classical oscillator is `kB T`. -/
lemma classicalOscillator_meanEnergy {T : Temperature} (hT : 0 < (T : ℝ)) :
    classicalOscillator.meanEnergy T = kB * T := by
  have hb : 0 < (T.β : ℝ) := by
    rw [β_toReal]
    exact one_div_pos.mpr (mul_pos kB_pos hT)
  have hnum : ∫ E in Set.Ioi (0 : ℝ), E * exp (-T.β * E) = ((T.β : ℝ) ^ 2)⁻¹ := by
    have := integral_rpow_mul_exp_neg_mul_rpow (p := 1) (q := 1) one_pos (by norm_num) hb
    simp only [rpow_one] at this
    rw [this, show (1 + 1 : ℝ) / 1 = 1 + 1 by norm_num, Gamma_add_one one_ne_zero, Gamma_one,
      show -(1 + 1) / (1 : ℝ) = -2 by norm_num, rpow_neg hb.le, rpow_two]
    ring
  have hden : ∫ E in Set.Ioi (0 : ℝ), exp (-T.β * E) = (T.β : ℝ)⁻¹ := by
    have := integral_exp_neg_mul_rpow (p := 1) one_pos hb
    simp only [rpow_one] at this
    rw [this, show (-1 : ℝ) / 1 = -1 by norm_num, rpow_neg_one,
      show (1 : ℝ) / 1 + 1 = 1 + 1 by norm_num, Gamma_add_one one_ne_zero, Gamma_one, mul_one,
      mul_one]
  rw [meanEnergy_eq_ratio_of_integrals]
  change (∫ E in Set.Ioi (0 : ℝ), E * exp (-T.β * E)) /
    (∫ E in Set.Ioi (0 : ℝ), exp (-T.β * E)) = _
  rw [hnum, hden, β_toReal]
  field_simp

/-- The quantized mean energy lies strictly below the classical one, `kB T`. -/
lemma quantizedOscillator_meanEnergy_lt {ε : ℝ} (hε : 0 < ε) {T : Temperature}
    (hT : 0 < (T : ℝ)) :
    (quantizedOscillator ε).meanEnergy T < classicalOscillator.meanEnergy T := by
  have hb : 0 < (T.β : ℝ) * ε := by
    rw [β_toReal]
    exact mul_pos (one_div_pos.mpr (mul_pos kB_pos hT)) hε
  have he : (T.β : ℝ) * ε < exp (T.β * ε) - 1 := by
    linarith [add_one_lt_exp hb.ne']
  rw [quantizedOscillator_meanEnergy hε hT, classicalOscillator_meanEnergy hT,
    div_lt_iff₀ (hb.trans he)]
  calc ε = kB * T * (T.β * ε) := by
        rw [β_toReal]
        field_simp [kB_pos.ne', hT.ne']
    _ < kB * T * (exp (T.β * ε) - 1) := mul_lt_mul_of_pos_left he (mul_pos kB_pos hT)

/-!

## C. Planck's law and the Rayleigh–Jeans law

-/

/-- Planck's law is `2 ν² / c²` times the mean energy of the oscillator of spacing `h ν`. -/
lemma spectralRadiance_eq_meanEnergy (B : BlackBody) (c : SpeedOfLight) {ν : ℝ} (hν : 0 < ν)
    (hT : 0 < (B.T : ℝ)) :
    B.spectralRadiance c ν =
      2 * ν ^ 2 / (c : ℝ) ^ 2 * (quantizedOscillator (h * ν)).meanEnergy B.T := by
  rw [quantizedOscillator_meanEnergy (mul_pos h_pos hν) hT, spectralRadiance,
    ite_eq_left hν, β_toReal, one_div_mul_eq_div]
  have hc := (pow_pos c.val_pos 2).ne'
  have he : exp (h * ν / (kB * B.T)) - 1 ≠ 0 :=
    (sub_pos.mpr (one_lt_exp_iff.mpr (div_pos (mul_pos h_pos hν) (mul_pos kB_pos hT)))).ne'
  field_simp

/-- The Rayleigh–Jeans spectral radiance `2 ν² kB T / c²` of a black body `B`. -/
noncomputable def rayleighJeans (B : BlackBody) (c : SpeedOfLight) (ν : ℝ) : ℝ :=
  2 * ν ^ 2 * kB * B.T / (c : ℝ) ^ 2

/-- The Rayleigh–Jeans law is `2 ν² / c²` times the mean energy of the classical oscillator. -/
lemma rayleighJeans_eq_meanEnergy (B : BlackBody) (c : SpeedOfLight) (ν : ℝ)
    (hT : 0 < (B.T : ℝ)) :
    B.rayleighJeans c ν = 2 * ν ^ 2 / (c : ℝ) ^ 2 * classicalOscillator.meanEnergy B.T := by
  rw [classicalOscillator_meanEnergy hT, rayleighJeans]
  ring

/-- Planck's law lies strictly below the Rayleigh–Jeans law at every positive frequency and
every positive temperature. -/
theorem spectralRadiance_lt_rayleighJeans (B : BlackBody) (c : SpeedOfLight) {ν : ℝ}
    (hν : 0 < ν) (hT : 0 < (B.T : ℝ)) :
    B.spectralRadiance c ν < B.rayleighJeans c ν := by
  rw [spectralRadiance_eq_meanEnergy B c hν hT, rayleighJeans_eq_meanEnergy B c ν hT]
  exact mul_lt_mul_of_pos_left (quantizedOscillator_meanEnergy_lt (mul_pos h_pos hν) hT)
    (by have := c.val_pos; positivity)

end BlackBody
