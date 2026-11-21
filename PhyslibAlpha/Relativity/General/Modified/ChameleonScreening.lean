/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!

# Chameleon screening and thin-shell suppression

Density-dependent scalar mass, Compton range contraction, Yukawa suppression, and thin-shell
screening of fifth forces.

## i. Overview

Scalar–tensor and `f(R)` models evade solar-system bounds (`γ = 1/2` in unscreened metric `f(R)`)
through chameleon screening: in high-density environments the effective scalar mass `m = √(c ρ)`
grows, shrinking the Compton wavelength `λ = 1/m` and confining the fifth force of massive bodies
to a thin outer shell of fractional thickness `Δ`.

This module formalises both halves of the mechanism:

- the environment chain `density ↑ ⇒ mass ↑ ⇒ range ↓ ⇒ Yukawa suppression` (`e^{-1} < 1/2`);
- the thin-shell exterior profile `φ(r) = φ∞ - Q/r` and fifth-force ratio `Δ = Q / (Φ R)`,
  showing `Δ ≤ ε` caps the fifth force at `ε` times gravity whereas `Δ ≥ 1` leaves an
  order-one unscreened fifth force.

## ii. Key results

- `chameleonMass`, `range`, `yukawaRatio` : effective mass, Compton range, and Yukawa factor.
- `chameleonMass_mono`, `chameleon_range_shrinks`, `yukawaRatio_lt_half` : monotonicity and
  suppression beyond one Compton wavelength.
- `thinShell`, `screeningFactor`, `thin_shell_suppressed`, `screeningFactor_eq_one_iff` :
  thin-shell cap `min Δ 1`.
- `profile`, `hasDerivAt_profile`, `forceRatio_thin_shell`, `thin_shell_weak`,
  `thick_shell_strong` : exterior scalar profile and screened vs unscreened fifth-force bounds.

## iii. Table of contents

- A. Environment-dependent mass, range, and Yukawa suppression
- B. Thin-shell screening factor and exterior profile

## iv. References

* None.

-/

@[expose] public section

namespace GeneralRelativity

namespace ChameleonScreening

/-!

## A. Environment-dependent mass, range, and Yukawa suppression

-/

/-- Scalar mass-squared proportional to ambient density: `m² = ρ c`. -/
noncomputable def chameleonMassSq (ρ c : ℝ) : ℝ := ρ * c

/-- The chameleon scalar mass `m = √(ρ c)`. -/
noncomputable def chameleonMass (ρ c : ℝ) : ℝ := Real.sqrt (ρ * c)

/-- A denser environment produces a heavier chameleon scalar. -/
lemma chameleonMass_mono {ρ₁ ρ₂ c : ℝ} (hc : 0 ≤ c) (h : ρ₁ ≤ ρ₂) :
    chameleonMass ρ₁ c ≤ chameleonMass ρ₂ c :=
  Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right h hc)

/-- Compton wavelength `λ = 1 / m` of a scalar of mass `m`. -/
noncomputable def range (m : ℝ) : ℝ := 1 / m

/-- A heavier scalar has a shorter Compton range. -/
lemma range_antitone {m₁ m₂ : ℝ} (h₁ : 0 < m₁) (h : m₁ ≤ m₂) :
    range m₂ ≤ range m₁ :=
  one_div_le_one_div_of_le h₁ h

/-- In a denser environment, the chameleon Compton range shrinks. -/
lemma chameleon_range_shrinks {ρ₁ ρ₂ c : ℝ} (hpos : 0 < chameleonMass ρ₁ c)
    (hc : 0 ≤ c) (h : ρ₁ ≤ ρ₂) :
    range (chameleonMass ρ₂ c) ≤ range (chameleonMass ρ₁ c) :=
  range_antitone hpos (chameleonMass_mono hc h)

/-- Yukawa suppression factor `e^{-x}` at dimensionless distance `x = r / λ`. -/
noncomputable def yukawaRatio (x : ℝ) : ℝ := Real.exp (-x)

/-- At one Compton wavelength, `e^{-1} < 1/2`. -/
lemma exp_neg_one_lt_half : Real.exp (-1) < 1 / 2 := by
  rw [Real.exp_neg]
  simpa using one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 2)
    (by linarith [Real.exp_one_gt_d9])

/-- Beyond one Compton range (`r ≥ λ`), the Yukawa factor drops below `1/2`. -/
lemma yukawaRatio_lt_half {x : ℝ} (h : 1 ≤ x) : yukawaRatio x < 1 / 2 := by
  have h1 : yukawaRatio x ≤ Real.exp (-1) := by
    simp only [yukawaRatio]
    exact Real.exp_le_exp.mpr (by linarith)
  linarith [exp_neg_one_lt_half]

/-!

## B. Thin-shell screening factor and exterior profile

-/

/-- Thin-shell parameter `Δ = |δφ| / (2 β M_pl |Φ_N|)`. -/
noncomputable def thinShell (dphi β Mpl Phi : ℝ) : ℝ :=
  |dphi| / (2 * β * Mpl * |Phi|)

/-- Surviving fraction `min Δ 1` of the unscreened fifth force. -/
noncomputable def screeningFactor (Δ : ℝ) : ℝ := min Δ 1

/-- Non-negativity of the thin-shell parameter for positive coupling and potential scale. -/
lemma thinShell_nonneg {dphi β Mpl Phi : ℝ} (h : 0 ≤ 2 * β * Mpl * |Phi|) :
    0 ≤ thinShell dphi β Mpl Phi :=
  div_nonneg (abs_nonneg dphi) h

/-- The screening factor never exceeds `Δ`. -/
lemma screeningFactor_le (Δ : ℝ) : screeningFactor Δ ≤ Δ := min_le_left _ _

/-- The screening factor never exceeds `1`. -/
lemma screeningFactor_le_one (Δ : ℝ) : screeningFactor Δ ≤ 1 := min_le_right _ _

/-- Thin-shell suppression: `Δ ≤ ε` implies `screeningFactor Δ ≤ ε`. -/
lemma thin_shell_suppressed {Δ ε : ℝ} (h : Δ ≤ ε) : screeningFactor Δ ≤ ε :=
  (screeningFactor_le Δ).trans h

/-- The external fifth-force screening factor saturates at `1` if and only if `1 ≤ Δ`. -/
lemma screeningFactor_eq_one_iff (Δ : ℝ) : screeningFactor Δ = 1 ↔ 1 ≤ Δ :=
  min_eq_right_iff

/-- Exterior scalar profile `φ(r) = φ∞ - Q / r` outside a spherical body. -/
noncomputable def profile (φinf Q r : ℝ) : ℝ := φinf - Q / r

/-- The radial gradient of the exterior profile is `Q / r²`. -/
lemma hasDerivAt_profile (φinf Q r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (profile φinf Q) (Q / r ^ 2) r := by
  change HasDerivAt (fun s : ℝ => φinf - Q / s) (Q / r ^ 2) r
  have hinv : HasDerivAt (fun s : ℝ => s⁻¹) (-1 / r ^ 2) r :=
    HasDerivAt.inv (hasDerivAt_id r) hr
  have hQ : HasDerivAt (fun s : ℝ => Q * s⁻¹) (Q * (-1 / r ^ 2)) r :=
    HasDerivAt.const_mul Q hinv
  have hsub : HasDerivAt (fun s : ℝ => φinf - Q * s⁻¹) (0 - Q * (-1 / r ^ 2)) r :=
    (hasDerivAt_const r φinf).sub hQ
  have hval : (0 - Q * (-1 / r ^ 2)) = Q / r ^ 2 := by
    field_simp
    ring
  rw [hval] at hsub
  exact hsub

/-- Fifth-force ratio `(Q / r²) / (Φ R / r²)` relative to Newtonian surface gravity. -/
noncomputable def forceRatio (Q Phi R r : ℝ) : ℝ := (Q / r ^ 2) / (Phi * R / r ^ 2)

/-- Away from `r = 0`, the fifth-force ratio simplifies to `Q / (Φ R)`. -/
lemma forceRatio_eq (Q Phi R r : ℝ) (hr : r ≠ 0) :
    forceRatio Q Phi R r = Q / (Phi * R) := by
  simp only [forceRatio]
  have hr2 : r ^ 2 ≠ 0 := pow_ne_zero 2 hr
  field_simp

/-- With thin-shell scalar charge `Q = Δ Φ R`, the exterior fifth force is `Δ` times gravity. -/
lemma forceRatio_thin_shell (Δ Phi R r : ℝ) (h : Phi * R ≠ 0) (hr : r ≠ 0) :
    forceRatio (Δ * Phi * R) Phi R r = Δ := by
  have hPhi : Phi ≠ 0 := (mul_ne_zero_iff.mp h).1
  have hR : R ≠ 0 := (mul_ne_zero_iff.mp h).2
  rw [forceRatio_eq _ Phi R r hr]
  field_simp

/-- The exterior profile evaluated at the stellar surface `r = R` gives `φ(R) = φ∞ - Δ Φ`. -/
lemma profile_surface (φinf Δ Phi R : ℝ) (hR : R ≠ 0) :
    profile φinf (Δ * Phi * R) R = φinf - Δ * Phi := by
  simp only [profile]
  field_simp

/-- Thin shell implies weak fifth force: `Δ ≤ ε` caps the fifth-force ratio at `ε`. -/
lemma thin_shell_weak (Δ ε Phi R r : ℝ) (hPR : Phi * R ≠ 0) (hr : r ≠ 0)
    (h : Δ ≤ ε) : forceRatio (Δ * Phi * R) Phi R r ≤ ε := by
  rw [forceRatio_thin_shell Δ Phi R r hPR hr]
  exact h

/-- Thick shell implies an order-one unscreened fifth force (`1 ≤ forceRatio`). -/
lemma thick_shell_strong (Δ Phi R r : ℝ) (hPR : Phi * R ≠ 0) (hr : r ≠ 0)
    (h : 1 ≤ Δ) : 1 ≤ forceRatio (Δ * Phi * R) Phi R r := by
  rw [forceRatio_thin_shell Δ Phi R r hPR hr]
  exact h

end ChameleonScreening

end GeneralRelativity
