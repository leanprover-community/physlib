/-
Copyright (c) 2026 AMPS formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AMPS formalization contributors
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# The operating window for the AMPS mining detector

Detector scales and backreaction.

## i. Overview

Appendix C of Almheiri, Marolf, Polchinski and Sully, arXiv:1207.3123v4,
gives scaling estimates for lowering a small detector into the thermal
atmosphere of a Schwarzschild black hole on cosmic strings. Work in Planck
units. Thus all lengths and times are measured in Planck lengths and all
energies in Planck energies. The spacetime dimension is `d = 4 + k`.

The following expressions are representatives of the paper's orders of
magnitude. The apparatus energy budgets two full strings and the detector.
The support structure is treated as external, as in the budget of Eq. (C.1).
The area expression is the estimated shear contribution of Eq. (C.5).
An arbitrary separation factor in the result can absorb fixed multiplicative
constants in these estimates. Estimates of absorption, mechanical stability,
net work recovered, and the Raychaudhuri shear integral enter the paper's
physical argument; the result here verifies compatibility of their scales.

## ii. Key results

* `detector_scales`
* `mining_window`

## iii. Table of contents

- A. Detector scales and backreaction

## iv. References

* [ref: Almheiri2013]

## A. Detector scales and backreaction
-/

@[expose] public section

namespace AMPS.MiningScale

noncomputable section

/-- Detector parameter, horizon radius, operating proper height, and duration
measured at infinity, in the units described above. -/
structure Apparatus where
  /-- Fixed ratio of the detector size to its operating depth. -/
  ε : ℝ
  /-- Schwarzschild radius in Planck lengths. -/
  rs : ℝ
  /-- Static proper distance of the detector from the horizon. -/
  L : ℝ
  /-- Asymptotically measured duration of the apparatus motion. -/
  t : ℝ

namespace Apparatus

/-- Linear size of the detector. -/
def size (a : Apparatus) := a.ε * a.L

/-- Rest mass of the unexcited detector. -/
def mass (a : Apparatus) := 1 / (a.ε * a.L)

/-- Near-horizon local temperature and the typical energy of an absorbed quantum. -/
def temperature (a : Apparatus) := 1 / a.L

/-- String tension scale required to hold the detector at proper height `L`. -/
def tension (a : Apparatus) := a.mass / a.L

/-- Radius of the external support. -/
def supportRadius (a : Apparatus) := a.rs / a.ε

/-- String and detector energy charged against the black hole mass. -/
def energyBudget (a : Apparatus) := 2 * a.tension * a.supportRadius + a.mass

/-- Black hole mass scale for `d = 4 + k`. -/
def blackHoleMass (a : Apparatus) (k : ℕ) := a.rs ^ (k + 1)

/-- Evaporation time scale for `d = 4 + k`. -/
def evaporationTime (a : Apparatus) (k : ℕ) := a.rs ^ (k + 3)

/-- Shear-induced area growth in Planck area units, using the duration of the motion. -/
def shearArea (a : Apparatus) (k : ℕ) :=
  a.rs ^ 3 / (a.ε ^ 2 * a.L * a.t ^ 2) * (1 / a.L) ^ (k + 2)

end Apparatus

/-- The detector is smaller than its height by `ε`. Its local thermal
energy gain is `ε` of its rest mass. The tension supports the detector
and the string width is `√ε L`. Redshifting the absorbed quantum by
the near-horizon lapse scale `L/rs` gives the Hawking energy scale. -/
lemma detector_scales (a : Apparatus) (he : 0 < a.ε) (hL : 0 < a.L) (hs : 0 < a.rs) :
    a.size / a.L = a.ε ∧ a.temperature = a.ε * a.mass ∧
    a.tension * a.L = a.mass ∧ a.temperature ^ 2 = a.ε * a.tension ∧
    a.tension * (Real.sqrt a.ε * a.L) ^ 2 = 1 ∧
    a.temperature * (a.L / a.rs) = 1 / a.rs := by
  dsimp [Apparatus.size, Apparatus.temperature, Apparatus.tension, Apparatus.mass]
  rw [mul_pow, Real.sq_sqrt he.le]
  exact ⟨by field_simp, by field_simp, by field_simp, by field_simp,
    by field_simp, by field_simp⟩

/-- For a prescribed dimensionless hierarchy `H`, these compare the height
to the Planck and curvature scales, the apparatus energy to the black hole
mass, the height's tidal safety power to the local mass/temperature ratio,
the wait time of order `rs` and the support travel time to the motion time,
the total motion time to evaporation, and the dissipative area to one
Planck area. Large `rs/L` is the angular-momentum scale being mined. -/
structure OperatingWindow (a : Apparatus) (k : ℕ) (H : ℝ) : Prop where
  abovePlanck : H < a.L
  angular : H < a.rs / a.L
  stableDetector : a.temperature < a.mass
  coldString : a.temperature ^ 2 < a.tension
  smallApparatus : H * a.energyBudget < a.blackHoleMass k
  smallTide : H * (a.mass / a.temperature) < a.L ^ (k + 2)
  absorptionTime : H * a.rs < a.t
  supportTravel : H * a.supportRadius < a.t
  beforeEvaporation : H * a.t < a.evaporationTime k
  smallArea : H * a.shearArea k < 1

/-- Fix the detector parameter `0 < ε < 1`, spacetime dimension `4+k`,
and an arbitrary hierarchy `H ≥ 1` independently of the black hole.
For every sufficiently large `B = √rs` the explicit choice `L = B` and
`t = B³ = √(rs³)` realizes all the inequalities simultaneously.
Thus the angular scale grows while `ε` stays fixed. -/
lemma mining_window (k : ℕ) {ε H B : ℝ} (he : 0 < ε) (he' : ε < 1) (hH : 1 ≤ H)
    (hlarge : H * (1 + 2 / ε ^ 2 + 1 / ε) < B) :
    OperatingWindow ⟨ε, B ^ 2, B, B ^ 3⟩ k H := by
  have hHp := lt_of_lt_of_le zero_lt_one hH
  have hi := one_div_pos.mpr he
  have hii := one_div_pos.mpr (sq_pos_of_pos he)
  have htwo : 2 / ε ^ 2 = 1 / ε ^ 2 + 1 / ε ^ 2 := by ring
  have small {c : ℝ} (hc : c ≤ 1 + 2 / ε ^ 2 + 1 / ε) : H * c < B :=
    (mul_le_mul_of_nonneg_left hc hHp.le).trans_lt hlarge
  have hscale : H < B := by
    simpa only [mul_one] using small (show 1 ≤ 1 + 2 / ε ^ 2 + 1 / ε by linarith)
  have hb : 1 < B := hH.trans_lt hscale
  have hbpos := zero_lt_one.trans hb
  have henergy := small (show 2 / ε ^ 2 + 1 / ε ≤ 1 + 2 / ε ^ 2 + 1 / ε by linarith)
  have htide : H / ε < B := by
    simpa only [mul_one_div] using small (show 1 / ε ≤ 1 + 2 / ε ^ 2 + 1 / ε by linarith)
  have harea : H / ε ^ 2 < B := by
    simpa only [mul_one_div] using small (show 1 / ε ^ 2 ≤ 1 + 2 / ε ^ 2 + 1 / ε by linarith)
  have hpows (i j : ℕ) (h : i ≤ j) : B ^ i ≤ B ^ j := pow_le_pow_right₀ hb.le h
  have hpow (j : ℕ) (h : 1 ≤ j) : B ≤ B ^ j := by simpa using hpows 1 j h
  have hm : 1 / (ε * B) ≤ 1 / ε :=
    one_div_le_one_div_of_le he (le_mul_of_one_le_right he.le hb.le)
  have hstr : 2 * (1 / (ε * B) / B) * (B ^ 2 / ε) = 2 / ε ^ 2 := by field_simp
  have ht : 1 / (ε * B) / (1 / B) = 1 / ε := by field_simp
  have hshear : (B ^ 2) ^ 3 / (ε ^ 2 * B * (B ^ 3) ^ 2) * (1 / B) ^ (k + 2) =
      1 / (ε ^ 2 * B ^ (k + 3)) := by
    simp only [pow_add, one_div_pow]
    field_simp
  constructor
  · exact hscale
  · change H < B ^ 2 / B
    rwa [sq, mul_div_cancel_right₀ _ hbpos.ne']
  · change 1 / B < 1 / (ε * B)
    exact one_div_lt_one_div_of_lt (mul_pos he hbpos) (mul_lt_of_lt_one_left hbpos he')
  · change (1 / B) ^ 2 < 1 / (ε * B) / B
    rw [show (1 / B) ^ 2 = (1 / B) / B by ring]
    exact div_lt_div_of_pos_right
      (one_div_lt_one_div_of_lt (mul_pos he hbpos) (mul_lt_of_lt_one_left hbpos he')) hbpos
  · change H * (2 * (1 / (ε * B) / B) * (B ^ 2 / ε) + 1 / (ε * B)) < (B ^ 2) ^ (k + 1)
    rw [hstr, ← pow_mul]
    exact (mul_le_mul_of_nonneg_left (add_le_add (le_refl (2 / ε ^ 2)) hm) hHp.le).trans_lt
      (henergy.trans_le (hpow (2 * (k + 1)) (by omega)))
  · change H * (1 / (ε * B) / (1 / B)) < B ^ (k + 2)
    rw [ht, mul_one_div]
    exact htide.trans_le (hpow _ (by omega))
  · change H * B ^ 2 < B ^ 3
    simpa only [pow_succ B 2, mul_comm (B ^ 2) B] using
      mul_lt_mul_of_pos_right hscale (sq_pos_of_pos hbpos)
  · change H * (B ^ 2 / ε) < B ^ 3
    calc
      _ = H / ε * B ^ 2 := by ring
      _ < B * B ^ 2 := mul_lt_mul_of_pos_right htide (sq_pos_of_pos hbpos)
      _ = _ := by ring
  · change H * B ^ 3 < (B ^ 2) ^ (k + 3)
    rw [← pow_mul]
    calc
      _ < B * B ^ 3 := mul_lt_mul_of_pos_right hscale (pow_pos hbpos _)
      _ = B ^ 4 := by ring
      _ ≤ _ := hpows _ _ (by omega)
  · change H * ((B ^ 2) ^ 3 / (ε ^ 2 * B * (B ^ 3) ^ 2) * (1 / B) ^ (k + 2)) < 1
    rw [hshear, mul_one_div, div_lt_one (mul_pos (sq_pos_of_pos he) (pow_pos hbpos _)), mul_comm]
    exact (div_lt_iff₀ (sq_pos_of_pos he)).mp (harea.trans_le (hpow _ (by omega)))

/-- The operating window is nonempty above any specified minimum black hole
radius, for a detector parameter chosen in advance. -/
lemma exists_mining_window (k : ℕ) (minRadius : ℝ) {ε H : ℝ}
    (he : 0 < ε) (he' : ε < 1) (hH : 1 ≤ H) :
    ∃ a : Apparatus, a.ε = ε ∧ minRadius < a.rs ∧ OperatingWindow a k H := by
  let floor := H * (1 + 2 / ε ^ 2 + 1 / ε)
  let B := max (max minRadius 1) floor + 1
  have hf : floor < B := (le_max_right _ _).trans_lt (lt_add_one _)
  have hprev : max minRadius 1 < B := (le_max_left _ _).trans_lt (lt_add_one _)
  have h1 : 1 < B := (le_max_right _ _).trans_lt hprev
  have hB : minRadius < B := (le_max_left _ _).trans_lt hprev
  refine ⟨⟨ε, B ^ 2, B, B ^ 3⟩, rfl, ?_, mining_window k he he' hH hf⟩
  exact hB.trans_le (by simpa [sq] using le_mul_of_one_le_right (zero_lt_one.trans h1).le h1.le)

/-- Appendix C, footnote following Eq. (C.2). Simultaneously deploying the
angular-mode count `(rs/L)^(d−2)` of these apparatuses is more restrictive
than the option to access any one mode. The strings alone force
`2 H rs² < ε² L^d` when the total energy budget is below `M_BH/H`.
Restoring lengths multiplies the left side by `ℓp^(d−2)`. The count is
the paper's continuum scaling estimate for the number of channels. -/
lemma full_array_depth (a : Apparatus) (k : ℕ) {H : ℝ} (hH : 0 < H)
    (he : 0 < a.ε) (hL : 0 < a.L) (hs : 0 < a.rs)
    (hbudget : H * ((a.rs / a.L) ^ (k + 2) * a.energyBudget) < a.blackHoleMass k) :
    2 * H * a.rs ^ 2 < a.ε ^ 2 * a.L ^ (k + 4) := by
  let N := (a.rs / a.L) ^ (k + 2)
  have hn : 0 ≤ N := (pow_pos (div_pos hs hL) _).le
  have hm : 0 < a.blackHoleMass k := pow_pos hs _
  have hstring : 2 * a.tension * a.supportRadius ≤ a.energyBudget :=
    le_add_of_nonneg_right (one_div_pos.mpr (mul_pos he hL)).le
  have hratio : N * (2 * a.tension * a.supportRadius) / a.blackHoleMass k =
      2 * a.rs ^ 2 / (a.ε ^ 2 * a.L ^ (k + 4)) := by
    dsimp [N, Apparatus.tension, Apparatus.mass, Apparatus.supportRadius, Apparatus.blackHoleMass]
    simp only [div_pow, pow_add]
    field_simp
  have hsmall : H * (2 * a.rs ^ 2 / (a.ε ^ 2 * a.L ^ (k + 4))) < 1 := by
    rw [← hratio, ← mul_div_assoc, div_lt_one hm]
    exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hstring hn) hH.le).trans_lt hbudget
  rw [← mul_div_assoc, div_lt_one (mul_pos (sq_pos_of_pos he) (pow_pos hL _))] at hsmall
  linarith only [hsmall]

end
end AMPS.MiningScale
