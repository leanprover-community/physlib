/-
Copyright (c) 2026 Philippe Kevorkian. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philippe Kevorkian
-/
module

public import Physlib.QuantumMechanics.Hydrogen.Basic
public import Physlib.Relativity.SpeedOfLight
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

Definitions:
- `rydbergEnergy` : the Rydberg energy `Ry = m k ^ 2 / (2 ℏ ^ 2)`.
- `levelIndex` : the effective principal quantum number `L n = n + (d - 1) / 2`.
- `energyLevel` : the Bohr levels `E_n = -Ry / L n ^ 2`.
- `transitionFrequency` : the frequency `ν = (E_{n₂} - E_{n₁}) / h` of the photon emitted in
    the transition from `n₂` to `n₁`, and `wavelength` its wavelength `c / ν`.
- `rydbergFrequency` : the Rydberg frequency `R_ν = Ry / h`.
- `lymanFrequency`, `balmerFrequency`, `paschenFrequency` : the three classical series.

Lemmas:
- `energyLevel_strictMono` : the Bohr levels increase strictly with `n` when `2 ≤ d`
    and `k ≠ 0`.
- `transitionFrequency_eq` : the Rydberg formula `ν = R_ν (1 / L n₁ ^ 2 - 1 / L n₂ ^ 2)`.
- `wavelength_inv` : its wavenumber form `1 / λ = (R_ν / c) (1 / L n₁ ^ 2 - 1 / L n₂ ^ 2)`.
- `tendsto_transitionFrequency` : the series limit `ν → R_ν / L n₁ ^ 2` as `n₂ → ∞`.
- `balmerFrequency_lt_lymanFrequency` : for `2 ≤ d ≤ 5`, every Balmer line lies below every
    Lyman line.

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

/-- The defining formula of the Rydberg energy. -/
lemma rydbergEnergy_eq : H.rydbergEnergy = H.m * H.k ^ 2 / (2 * (ℏ : ℝ) ^ 2) := rfl

/-- The level index `n + (d - 1) / 2` of the `n`-th Bohr level; for `d = 3` it is the principal
quantum number `n + 1`. -/
def levelIndex (n : ℕ) : ℝ := n + ((H.d : ℝ) - 1) / 2

/-- The defining formula of the level index. -/
lemma levelIndex_eq (n : ℕ) : H.levelIndex n = n + ((H.d : ℝ) - 1) / 2 := rfl

/-- The `n`-th Bohr level `E_n = -Ry / (n + (d - 1) / 2) ^ 2`.

These are the bound-state energies expected for the hydrogen Hamiltonian; that they form its
point spectrum is not proved here. For `d = 1` and `n = 0` the level index vanishes and the value
is `0` by the convention `x / 0 = 0`. -/
def energyLevel (n : ℕ) : ℝ := -H.rydbergEnergy / H.levelIndex n ^ 2

/-- The defining formula of the Bohr levels. -/
lemma energyLevel_eq (n : ℕ) : H.energyLevel n = -H.rydbergEnergy / H.levelIndex n ^ 2 := rfl

/-- The Rydberg energy is non-negative. -/
@[simp]
lemma rydbergEnergy_nonneg : 0 ≤ H.rydbergEnergy :=
  div_nonneg (mul_nonneg H.m_pos.le (sq_nonneg _)) (by positivity)

/-- The Rydberg energy is positive when `k ≠ 0`. -/
@[simp]
lemma rydbergEnergy_pos (hk : H.k ≠ 0) : 0 < H.rydbergEnergy :=
  div_pos (mul_pos H.m_pos (pow_two_pos_of_ne_zero hk)) (mul_pos two_pos (pow_pos ℏ_pos 2))

/-- The Rydberg energy vanishes when `k = 0`. -/
@[simp]
lemma rydbergEnergy_eq_zero (hk : H.k = 0) : H.rydbergEnergy = 0 := by
  simp [rydbergEnergy_eq, hk]

/-- The level index is non-negative when `d ≠ 0`. -/
@[simp]
lemma levelIndex_nonneg [NeZero H.d] (n : ℕ) : 0 ≤ H.levelIndex n := by
  have hd : (1 : ℝ) ≤ H.d := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne H.d)
  rw [levelIndex_eq]
  linarith

/-- The level index is positive when `2 ≤ d`. -/
@[simp]
lemma levelIndex_pos (hd : 2 ≤ H.d) (n : ℕ) : 0 < H.levelIndex n := by
  have hd' : (2 : ℝ) ≤ H.d := by exact_mod_cast hd
  rw [levelIndex_eq]
  linarith

/-- The level index is strictly increasing. -/
lemma levelIndex_strictMono : StrictMono H.levelIndex := by
  intro n₁ n₂ hn
  have hn' : (n₁ : ℝ) < n₂ := by exact_mod_cast hn
  rw [levelIndex_eq, levelIndex_eq]
  linarith

/-- The level index is monotone. -/
lemma levelIndex_monotone : Monotone H.levelIndex := H.levelIndex_strictMono.monotone

/-- The Bohr levels are non-positive. -/
@[simp]
lemma energyLevel_nonpos (n : ℕ) : H.energyLevel n ≤ 0 := by
  simp [energyLevel_eq, neg_div, div_nonneg, sq_nonneg]

/-- The Bohr levels are negative when `2 ≤ d` and `k ≠ 0`. -/
@[simp]
lemma energyLevel_neg (hd : 2 ≤ H.d) (hk : H.k ≠ 0) (n : ℕ) : H.energyLevel n < 0 := by
  simp [energyLevel_eq, neg_div, hd, hk]

/-- The Bohr levels vanish when `k = 0`. -/
@[simp]
lemma energyLevel_eq_zero (hk : H.k = 0) (n : ℕ) : H.energyLevel n = 0 := by
  simp [energyLevel_eq, hk]

/-- The Bohr levels are strictly increasing when `2 ≤ d` and `k ≠ 0`. -/
lemma energyLevel_strictMono (hd : 2 ≤ H.d) (hk : H.k ≠ 0) : StrictMono H.energyLevel := by
  intro n₁ n₂ hn
  rw [energyLevel_eq, energyLevel_eq, neg_div, neg_div, neg_lt_neg_iff]
  exact div_lt_div_of_pos_left (H.rydbergEnergy_pos hk) (pow_pos (H.levelIndex_pos hd n₁) 2)
    (pow_lt_pow_left₀ (H.levelIndex_strictMono hn) (H.levelIndex_pos hd n₁).le two_ne_zero)

/-- The Bohr levels are monotone when `2 ≤ d`. The hypothesis on `d` cannot be dropped:
for `d = 1` the level index of `n = 0` vanishes, so that `E_0 = 0` by the convention
`x / 0 = 0` while every other level is negative. -/
lemma energyLevel_monotone (hd : 2 ≤ H.d) : Monotone H.energyLevel := by
  by_cases hk : H.k = 0
  · exact fun _ _ _ => by simp [hk]
  · exact (H.energyLevel_strictMono hd hk).monotone

/-!

## B. Transitions and the Rydberg formula

A transition from the level `n₂` down to the level `n₁` emits a photon of energy
`E_{n₂} - E_{n₁}`, frequency `ν = (E_{n₂} - E_{n₁}) / h` and wavelength `λ = c / ν`, with `c` the
speed of light. The Rydberg formula expresses these through the Rydberg frequency `R_ν = Ry / h`,
the frequency of a photon carrying the Rydberg energy.

The same definitions are used for any pair of levels. When `2 ≤ d` and `k ≠ 0` and `n₂ < n₁`,
the level `n₂` lies below `n₁`: the transition from `n₂` to `n₁` goes up and absorbs a photon, and
the frequency and the wavelength defined here are then negative, their absolute values being
those of the absorbed photon. For `n₁ = n₂` there is no photon and the frequency is `0`.

-/

/-- The energy `E_{n₂} - E_{n₁}` of the transition from the level `n₂` to the level `n₁`. -/
def transitionEnergy (n₁ n₂ : ℕ) : ℝ := H.energyLevel n₂ - H.energyLevel n₁

/-- The defining formula of the transition energy. -/
lemma transitionEnergy_eq_sub (n₁ n₂ : ℕ) :
    H.transitionEnergy n₁ n₂ = H.energyLevel n₂ - H.energyLevel n₁ := rfl

/-- The frequency `(E_{n₂} - E_{n₁}) / h` of the transition from `n₂` to `n₁`. When `2 ≤ d` and
`k ≠ 0`, it is positive for `n₁ < n₂` (`transitionFrequency_pos`): the transition emits a photon
of this frequency. For `n₂ < n₁` it is negative (`transitionFrequency_neg`): the transition goes
up in energy and absorbs a photon, whose frequency is the absolute value `(E_{n₁} - E_{n₂}) / h`
(`transitionFrequency_swap`). For `n₁ = n₂` it is `0` (`transitionFrequency_self`). -/
def transitionFrequency (n₁ n₂ : ℕ) : ℝ := H.transitionEnergy n₁ n₂ / (h : ℝ)

/-- The defining formula of the transition frequency. -/
lemma transitionFrequency_eq_div (n₁ n₂ : ℕ) :
    H.transitionFrequency n₁ n₂ = H.transitionEnergy n₁ n₂ / (h : ℝ) := rfl

/-- Exchanging the two levels changes the sign of the transition frequency. -/
lemma transitionFrequency_swap (n₁ n₂ : ℕ) :
    H.transitionFrequency n₂ n₁ = -H.transitionFrequency n₁ n₂ := by
  rw [transitionFrequency_eq_div, transitionFrequency_eq_div, transitionEnergy_eq_sub,
    transitionEnergy_eq_sub, ← neg_div, neg_sub]

/-- The transition frequency between a level and itself is `0`. -/
@[simp]
lemma transitionFrequency_self (n : ℕ) : H.transitionFrequency n n = 0 := by
  simp [transitionFrequency_eq_div, transitionEnergy_eq_sub]

/-- The Rydberg frequency `R_ν = Ry / h`, the frequency of a photon whose energy is the Rydberg
energy. -/
abbrev rydbergFrequency : ℝ := H.rydbergEnergy / (h : ℝ)

/-- The wavelength `c / ν` of the photon emitted in the transition from `n₂` to `n₁`, with `c` the
speed of light. When `2 ≤ d` and `k ≠ 0` and `n₂ < n₁`, the frequency is negative and so is this
wavelength; its absolute value is the wavelength of the photon absorbed in the transition from
`n₂` up to `n₁`. For `n₁ = n₂` there is no photon: the frequency is `0` and the value `c / 0 = 0`
is a junk value, not a wavelength. -/
def wavelength (c : SpeedOfLight) (n₁ n₂ : ℕ) : ℝ := c / H.transitionFrequency n₁ n₂

/-- The defining formula of the wavelength. -/
lemma wavelength_eq_div (c : SpeedOfLight) (n₁ n₂ : ℕ) :
    H.wavelength c n₁ n₂ = c / H.transitionFrequency n₁ n₂ := rfl

/-- The Rydberg formula for the transition energy,
`E_{n₂} - E_{n₁} = Ry (1 / L n₁ ^ 2 - 1 / L n₂ ^ 2)`. -/
lemma transitionEnergy_eq (n₁ n₂ : ℕ) :
    H.transitionEnergy n₁ n₂ =
      H.rydbergEnergy * (1 / H.levelIndex n₁ ^ 2 - 1 / H.levelIndex n₂ ^ 2) := by
  rw [transitionEnergy_eq_sub, energyLevel_eq, energyLevel_eq]
  ring

/-- The Rydberg frequency in terms of the mass, the coupling constant and `ℏ`,
`R_ν = m k ^ 2 / (4 π ℏ ^ 3)`, using `h = 2 π ℏ`. -/
lemma rydbergFrequency_eq : H.rydbergFrequency = H.m * H.k ^ 2 / (4 * π * (ℏ : ℝ) ^ 3) := by
  rw [rydbergFrequency, rydbergEnergy_eq, h_eq_two_pi_hbar]
  field

/-- The Rydberg frequency is non-negative. -/
@[simp]
lemma rydbergFrequency_nonneg : 0 ≤ H.rydbergFrequency :=
  div_nonneg H.rydbergEnergy_nonneg h_nonneg

/-- The Rydberg frequency is positive when `k ≠ 0`. Not `@[simp]`: since `rydbergFrequency` is an
abbreviation, `simp` already gets this from `rydbergEnergy_pos` and `h_pos`. -/
lemma rydbergFrequency_pos (hk : H.k ≠ 0) : 0 < H.rydbergFrequency :=
  div_pos (H.rydbergEnergy_pos hk) h_pos

/-- The Rydberg frequency vanishes when `k = 0`. -/
@[simp]
lemma rydbergFrequency_eq_zero (hk : H.k = 0) : H.rydbergFrequency = 0 := by
  simp [hk]

/-- The Rydberg formula for the frequency, `ν = R_ν (1 / L n₁ ^ 2 - 1 / L n₂ ^ 2)`. -/
lemma transitionFrequency_eq (n₁ n₂ : ℕ) :
    H.transitionFrequency n₁ n₂ =
      H.rydbergFrequency * (1 / H.levelIndex n₁ ^ 2 - 1 / H.levelIndex n₂ ^ 2) := by
  rw [transitionFrequency_eq_div, H.transitionEnergy_eq]
  show _ = H.rydbergEnergy / (h : ℝ) * _
  ring

/-- The frequency of a transition from `n₂` down to `n₁ < n₂` is positive when `2 ≤ d` and
`k ≠ 0`. -/
@[simp]
lemma transitionFrequency_pos (hd : 2 ≤ H.d) (hk : H.k ≠ 0) {n₁ n₂ : ℕ} (hn : n₁ < n₂) :
    0 < H.transitionFrequency n₁ n₂ :=
  div_pos (sub_pos.mpr (H.energyLevel_strictMono hd hk hn)) h_pos

/-- The frequency of a transition from `n₂` up to `n₁`, with `n₂ < n₁`, is negative when `2 ≤ d`
and `k ≠ 0`: the transition absorbs a photon. -/
lemma transitionFrequency_neg (hd : 2 ≤ H.d) (hk : H.k ≠ 0) {n₁ n₂ : ℕ} (hn : n₂ < n₁) :
    H.transitionFrequency n₁ n₂ < 0 := by
  rw [H.transitionFrequency_swap n₂ n₁, neg_lt_zero]
  exact H.transitionFrequency_pos hd hk hn

/-- The Rydberg formula for the wavenumber,
`1 / λ = (R_ν / c) (1 / L n₁ ^ 2 - 1 / L n₂ ^ 2)`. -/
lemma wavelength_inv (c : SpeedOfLight) (n₁ n₂ : ℕ) :
    (H.wavelength c n₁ n₂)⁻¹ =
      H.rydbergFrequency / c * (1 / H.levelIndex n₁ ^ 2 - 1 / H.levelIndex n₂ ^ 2) := by
  rw [wavelength_eq_div, inv_div, H.transitionFrequency_eq]
  ring

/-- For a fixed lower level, the transition frequency is strictly increasing in the upper level
when `2 ≤ d` and `k ≠ 0`. -/
lemma transitionFrequency_strictMono (hd : 2 ≤ H.d) (hk : H.k ≠ 0) (n₁ : ℕ) :
    StrictMono (H.transitionFrequency n₁) := by
  intro n₂ n₃ hn
  rw [H.transitionFrequency_eq, H.transitionFrequency_eq]
  refine mul_lt_mul_of_pos_left ?_ (H.rydbergFrequency_pos hk)
  have hL := H.levelIndex_pos hd n₂
  have := one_div_lt_one_div_of_lt (pow_pos hL 2)
    (pow_lt_pow_left₀ (H.levelIndex_strictMono hn) hL.le two_ne_zero)
  linarith

/-- For a fixed lower level, the transition frequency is monotone in the upper level when
`2 ≤ d`. The hypothesis on `k` can be dropped, but not the one on `d`: for `d = 1` the level
index of `n = 0` vanishes and `1 / L 0 ^ 2 = 0` by the convention `x / 0 = 0`. -/
lemma transitionFrequency_monotone (hd : 2 ≤ H.d) (n₁ : ℕ) :
    Monotone (H.transitionFrequency n₁) := by
  by_cases hk : H.k = 0
  · exact fun _ _ _ => by simp [H.transitionFrequency_eq, hk]
  · exact (H.transitionFrequency_strictMono hd hk n₁).monotone

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
abbrev lymanFrequency (n : ℕ) : ℝ := H.transitionFrequency 0 n

/-- The Balmer series: the transitions down to the level of index `1`. -/
abbrev balmerFrequency (n : ℕ) : ℝ := H.transitionFrequency 1 n

/-- The Paschen series: the transitions down to the level of index `2`. -/
abbrev paschenFrequency (n : ℕ) : ℝ := H.transitionFrequency 2 n

/-- For `2 ≤ d ≤ 5`, every Balmer line has a lower frequency than every Lyman line: the Balmer
series limit `R_ν / L 1 ^ 2` is at most the first Lyman line `R_ν (1 / L 0 ^ 2 - 1 / L 1 ^ 2)`,
which holds exactly when `2 L 0 ^ 2 ≤ L 1 ^ 2`, that is `d ^ 2 - 6 d + 1 ≤ 0`. This fails for
`6 ≤ d`: in dimension `6` the Balmer line `n₂ = 15` has exactly the frequency
`96 R_ν / 1225` of the first Lyman line, and the Balmer lines above it are faster still.

The Balmer lines are the transitions with `1 < n₂`, but that hypothesis is not needed here: for
`n₂ ≤ 1` the left-hand side is non-positive while the right-hand side is positive. -/
lemma balmerFrequency_lt_lymanFrequency (hd₂ : 2 ≤ H.d) (hd₅ : H.d ≤ 5) (hk : H.k ≠ 0)
    {n₂ n₃ : ℕ} (h₃ : 0 < n₃) : H.balmerFrequency n₂ < H.lymanFrequency n₃ := by
  have hd₂' : (2 : ℝ) ≤ H.d := by exact_mod_cast hd₂
  have hd₅' : (H.d : ℝ) ≤ 5 := by exact_mod_cast hd₅
  have hL0 : 0 < H.levelIndex 0 := H.levelIndex_pos hd₂ 0
  have hL1 : 0 < H.levelIndex 1 := H.levelIndex_pos hd₂ 1
  have key : 2 * H.levelIndex 0 ^ 2 ≤ H.levelIndex 1 ^ 2 := by
    rw [levelIndex_eq, levelIndex_eq]
    push_cast
    nlinarith [mul_nonneg (sub_nonneg.mpr hd₂') (sub_nonneg.mpr hd₅')]
  have hkey : 2 * (1 / H.levelIndex 1 ^ 2) ≤ 1 / H.levelIndex 0 ^ 2 := by
    have hle := one_div_le_one_div_of_le (pow_pos hL0 2)
      (by linarith : H.levelIndex 0 ^ 2 ≤ H.levelIndex 1 ^ 2 / 2)
    rw [one_div_div, div_eq_mul_one_div] at hle
    exact hle
  have hb : 0 < 1 / H.levelIndex n₂ ^ 2 :=
    one_div_pos.mpr (pow_pos (H.levelIndex_pos hd₂ n₂) 2)
  have hl : 1 / H.levelIndex n₃ ^ 2 ≤ 1 / H.levelIndex 1 ^ 2 :=
    one_div_le_one_div_of_le (pow_pos hL1 2)
      (pow_le_pow_left₀ hL1.le (H.levelIndex_monotone h₃) 2)
  show H.transitionFrequency 1 n₂ < H.transitionFrequency 0 n₃
  rw [H.transitionFrequency_eq, H.transitionFrequency_eq]
  refine mul_lt_mul_of_pos_left ?_ (H.rydbergFrequency_pos hk)
  linarith

end
end HydrogenAtom
end QuantumMechanics
