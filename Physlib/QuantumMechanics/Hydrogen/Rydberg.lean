/-
Copyright (c) 2026 Philippe Kevorkian. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philippe Kevorkian
-/
module

public import Physlib.QuantumMechanics.Hydrogen.Basic
/-!

# The Rydberg formula and the spectral series of the hydrogen atom

## i. Overview

The bound-state energies expected for the `d`-dimensional hydrogen atom with potential `-k / r`
are `E_n = -Ry / (n + (d - 1) / 2) ^ 2` for `n : ℕ`, with the Rydberg energy
`Ry = m k ^ 2 / (2 ℏ ^ 2)`. This module defines these Bohr levels and derives from them, by
algebra alone, the Rydberg formula for the energy, the frequency and the wavelength of the
photon emitted in a transition between two levels, together with the Lyman, Balmer and Paschen
series and their series limits.

The statement that these values are the point spectrum of the hydrogen Hamiltonian is not
proved here; it is a separate TODO of the `Basic` module. Nothing in this module depends on
the Hamiltonian.

## ii. Key results

- `energyLevel` defines the Bohr levels `E_n = -Ry / (n + (d - 1) / 2) ^ 2`; they are
  negative and increasing in `n` when `2 ≤ d` and `k ≠ 0`.
- `transitionFrequency_eq` is the Rydberg formula
  `ν = R_ν (1 / L n₁ ^ 2 - 1 / L n₂ ^ 2)` with `R_ν = m k ^ 2 / (4 π ℏ ^ 3) = Ry / h`, and
  `wavelength_inv` is its wavenumber form `1 / λ = (R_ν / c) (1 / L n₁ ^ 2 - 1 / L n₂ ^ 2)`.
- `tendsto_transitionFrequency` gives the series limit `ν → R_ν / L n₁ ^ 2`.
- `lymanFrequency`, `balmerFrequency` and `paschenFrequency` define the three classical series;
  `balmerFrequency_lt_lymanFrequency` shows that in dimension `3` every Balmer line lies below
  every Lyman line.

## iii. Table of contents

- A. The Bohr levels
- B. Transitions and the Rydberg formula
- C. The spectral series

## iv. References

* None.
-/

@[expose] public section

namespace QuantumMechanics
namespace HydrogenAtom
noncomputable section
open Constants Real Filter Topology

variable (H : HydrogenAtom)

/-!

## A. The Bohr levels

The Rydberg energy `Ry = m k ^ 2 / (2 ℏ ^ 2)` sets the scale of the spectrum, and the level
index `L n = n + (d - 1) / 2` is the effective principal quantum number in dimension `d`; for
`d = 3` it is `n + 1`, the usual principal quantum number, with `n = 0` the ground state.

-/

/-- The Rydberg energy of the atom, `Ry = m k ^ 2 / (2 ℏ ^ 2)`. -/
def rydbergEnergy : ℝ := H.m * H.k ^ 2 / (2 * (ℏ : ℝ) ^ 2)

/-- The level index `n + (d - 1) / 2` of the `n`-th Bohr level; for `d = 3` it is the principal
quantum number `n + 1`. -/
def levelIndex (n : ℕ) : ℝ := n + ((H.d : ℝ) - 1) / 2

/-- The `n`-th Bohr level `E_n = -Ry / (n + (d - 1) / 2) ^ 2`.

These are the bound-state energies expected for the hydrogen Hamiltonian; that they form its
point spectrum is not proved here. For `d = 1` and `n = 0` the level index vanishes and the value
is `0` by the convention `x / 0 = 0`. -/
def energyLevel (n : ℕ) : ℝ := -H.rydbergEnergy / H.levelIndex n ^ 2

/-- The Rydberg energy is positive when `k ≠ 0`. -/
lemma rydbergEnergy_pos (hk : H.k ≠ 0) : 0 < H.rydbergEnergy :=
  div_pos (mul_pos H.m_pos (pow_two_pos_of_ne_zero hk)) (mul_pos two_pos (pow_pos ℏ_pos 2))

/-- The level index is positive when `2 ≤ d`. -/
lemma levelIndex_pos (hd : 2 ≤ H.d) (n : ℕ) : 0 < H.levelIndex n := by
  have hd' : (2 : ℝ) ≤ H.d := by exact_mod_cast hd
  have hn : (0 : ℝ) ≤ n := n.cast_nonneg
  unfold levelIndex
  linarith

/-- The level index is strictly increasing. -/
lemma levelIndex_lt_levelIndex {n₁ n₂ : ℕ} (h : n₁ < n₂) : H.levelIndex n₁ < H.levelIndex n₂ := by
  have h' : (n₁ : ℝ) < n₂ := by exact_mod_cast h
  unfold levelIndex
  linarith

/-- The Bohr levels are negative when `2 ≤ d` and `k ≠ 0`. -/
lemma energyLevel_neg (hd : 2 ≤ H.d) (hk : H.k ≠ 0) (n : ℕ) : H.energyLevel n < 0 := by
  rw [energyLevel, neg_div, neg_lt_zero]
  exact div_pos (H.rydbergEnergy_pos hk) (pow_pos (H.levelIndex_pos hd n) 2)

/-- The Bohr levels are strictly increasing when `2 ≤ d` and `k ≠ 0`. -/
lemma energyLevel_lt_energyLevel (hd : 2 ≤ H.d) (hk : H.k ≠ 0) {n₁ n₂ : ℕ} (h : n₁ < n₂) :
    H.energyLevel n₁ < H.energyLevel n₂ := by
  unfold energyLevel
  rw [neg_div, neg_div, neg_lt_neg_iff]
  exact div_lt_div_of_pos_left (H.rydbergEnergy_pos hk) (pow_pos (H.levelIndex_pos hd n₁) 2)
    (pow_lt_pow_left₀ (H.levelIndex_lt_levelIndex h) (H.levelIndex_pos hd n₁).le two_ne_zero)

/-!

## B. Transitions and the Rydberg formula

A transition from the level `n₂` down to the level `n₁` emits a photon of energy
`E_{n₂} - E_{n₁}`, frequency `ν = (E_{n₂} - E_{n₁}) / h` and wavelength `λ = c / ν`, where the
speed of light `c` is taken as a parameter. The Rydberg formula expresses these through the
Rydberg frequency `R_ν = m k ^ 2 / (4 π ℏ ^ 3) = Ry / h`.

-/

/-- The energy `E_{n₂} - E_{n₁}` of the transition from the level `n₂` to the level `n₁`. -/
def transitionEnergy (n₁ n₂ : ℕ) : ℝ := H.energyLevel n₂ - H.energyLevel n₁

/-- The frequency `(E_{n₂} - E_{n₁}) / h` of the photon emitted in the transition from `n₂`
to `n₁`. -/
def transitionFrequency (n₁ n₂ : ℕ) : ℝ := H.transitionEnergy n₁ n₂ / (h : ℝ)

/-- The Rydberg frequency `R_ν = m k ^ 2 / (4 π ℏ ^ 3)`, equal to `Ry / h`. -/
def rydbergFrequency : ℝ := H.m * H.k ^ 2 / (4 * π * (ℏ : ℝ) ^ 3)

/-- The wavelength `c / ν` of the photon emitted in the transition from `n₂` to `n₁`, for a
speed of light `c`. -/
def wavelength (c : ℝ) (n₁ n₂ : ℕ) : ℝ := c / H.transitionFrequency n₁ n₂

/-- The Rydberg formula for the transition energy,
`E_{n₂} - E_{n₁} = Ry (1 / L n₁ ^ 2 - 1 / L n₂ ^ 2)`; an identity valid for every `d`. -/
lemma transitionEnergy_eq (n₁ n₂ : ℕ) :
    H.transitionEnergy n₁ n₂ =
      H.rydbergEnergy * (1 / H.levelIndex n₁ ^ 2 - 1 / H.levelIndex n₂ ^ 2) := by
  unfold transitionEnergy energyLevel
  ring

/-- The Rydberg frequency equals `Ry / h`, with `h = 2 π ℏ`. -/
lemma rydbergFrequency_eq : H.rydbergFrequency = H.rydbergEnergy / (h : ℝ) := by
  rw [rydbergFrequency, rydbergEnergy, show (h : ℝ) = 2 * π * (ℏ : ℝ) from rfl]
  field_simp
  ring

/-- The Rydberg frequency is positive when `k ≠ 0`. -/
lemma rydbergFrequency_pos (hk : H.k ≠ 0) : 0 < H.rydbergFrequency := by
  rw [H.rydbergFrequency_eq]
  exact div_pos (H.rydbergEnergy_pos hk) h_pos

/-- The Rydberg formula for the frequency, `ν = R_ν (1 / L n₁ ^ 2 - 1 / L n₂ ^ 2)`. -/
lemma transitionFrequency_eq (n₁ n₂ : ℕ) :
    H.transitionFrequency n₁ n₂ =
      H.rydbergFrequency * (1 / H.levelIndex n₁ ^ 2 - 1 / H.levelIndex n₂ ^ 2) := by
  rw [transitionFrequency, H.transitionEnergy_eq, H.rydbergFrequency_eq]
  ring

/-- The frequency of a transition from `n₂` down to `n₁ < n₂` is positive when `2 ≤ d` and
`k ≠ 0`. -/
lemma transitionFrequency_pos (hd : 2 ≤ H.d) (hk : H.k ≠ 0) {n₁ n₂ : ℕ} (h : n₁ < n₂) :
    0 < H.transitionFrequency n₁ n₂ :=
  div_pos (sub_pos.mpr (H.energyLevel_lt_energyLevel hd hk h)) h_pos

/-- The Rydberg formula for the wavenumber,
`1 / λ = (R_ν / c) (1 / L n₁ ^ 2 - 1 / L n₂ ^ 2)`; for `c = 0` both sides are `0`. -/
lemma wavelength_inv (c : ℝ) (n₁ n₂ : ℕ) :
    (H.wavelength c n₁ n₂)⁻¹ =
      H.rydbergFrequency / c * (1 / H.levelIndex n₁ ^ 2 - 1 / H.levelIndex n₂ ^ 2) := by
  rw [wavelength, inv_div, H.transitionFrequency_eq]
  ring

/-- For a fixed lower level, the transition frequency increases with the upper level when
`2 ≤ d` and `k ≠ 0`. -/
lemma transitionFrequency_lt_transitionFrequency (hd : 2 ≤ H.d) (hk : H.k ≠ 0) (n₁ : ℕ)
    {n₂ n₃ : ℕ} (h : n₂ < n₃) : H.transitionFrequency n₁ n₂ < H.transitionFrequency n₁ n₃ := by
  rw [H.transitionFrequency_eq, H.transitionFrequency_eq]
  refine mul_lt_mul_of_pos_left ?_ (H.rydbergFrequency_pos hk)
  have hL := H.levelIndex_pos hd n₂
  have := one_div_lt_one_div_of_lt (pow_pos hL 2)
    (pow_lt_pow_left₀ (H.levelIndex_lt_levelIndex h) hL.le two_ne_zero)
  linarith

/-- The series limit: as the upper level goes to infinity, the transition frequency to the
level `n₁` tends to `R_ν / L n₁ ^ 2`. -/
lemma tendsto_transitionFrequency (n₁ : ℕ) :
    Tendsto (fun n₂ : ℕ => H.transitionFrequency n₁ n₂) atTop
      (𝓝 (H.rydbergFrequency / H.levelIndex n₁ ^ 2)) := by
  have hL : Tendsto (fun n : ℕ => H.levelIndex n ^ 2) atTop atTop :=
    (tendsto_pow_atTop two_ne_zero).comp
      (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
  have hf : Tendsto (fun n : ℕ => 1 / H.levelIndex n ^ 2) atTop (𝓝 0) :=
    hL.inv_tendsto_atTop.congr fun n => by simp
  simp_rw [H.transitionFrequency_eq n₁, div_eq_mul_one_div H.rydbergFrequency]
  simpa using (tendsto_const_nhds.sub hf).const_mul H.rydbergFrequency

/-!

## C. The spectral series

The Lyman, Balmer and Paschen series collect the transitions down to the levels of index `0`,
`1` and `2`; for `d = 3` these are the levels `n = 1`, `2` and `3` of the usual numbering.

-/

/-- The Lyman series: the transitions down to the level of index `0`. -/
def lymanFrequency (n : ℕ) : ℝ := H.transitionFrequency 0 n

/-- The Balmer series: the transitions down to the level of index `1`. -/
def balmerFrequency (n : ℕ) : ℝ := H.transitionFrequency 1 n

/-- The Paschen series: the transitions down to the level of index `2`. -/
def paschenFrequency (n : ℕ) : ℝ := H.transitionFrequency 2 n

/-- In dimension `3`, every Balmer line has a lower frequency than every Lyman line: the Balmer
series limit is `R_ν / 4` while the first Lyman line is at `3 R_ν / 4`. This fails for `6 ≤ d`. -/
lemma balmerFrequency_lt_lymanFrequency (hd : H.d = 3) (hk : H.k ≠ 0) {n₂ n₃ : ℕ} (h₂ : 1 < n₂)
    (h₃ : 0 < n₃) : H.balmerFrequency n₂ < H.lymanFrequency n₃ := by
  have hL : ∀ n : ℕ, H.levelIndex n = n + 1 := fun n => by
    rw [levelIndex, hd]
    norm_num
  have hb : 0 < 1 / H.levelIndex n₂ ^ 2 := by
    rw [hL]
    positivity
  have hl : 1 / H.levelIndex n₃ ^ 2 ≤ 1 / 4 := by
    have h₃' : (1 : ℝ) ≤ n₃ := by exact_mod_cast h₃
    rw [hL]
    exact one_div_le_one_div_of_le (by norm_num) (by nlinarith)
  have hL1 : H.levelIndex 1 = 2 := by
    rw [hL]
    norm_num
  have hL0 : H.levelIndex 0 = 1 := by
    rw [hL]
    norm_num
  rw [balmerFrequency, lymanFrequency, H.transitionFrequency_eq, H.transitionFrequency_eq, hL1, hL0]
  refine mul_lt_mul_of_pos_left ?_ (H.rydbergFrequency_pos hk)
  nlinarith [hb, hl]

end
end HydrogenAtom
end QuantumMechanics
