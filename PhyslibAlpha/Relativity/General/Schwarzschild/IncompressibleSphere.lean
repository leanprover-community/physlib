/-
Copyright (c) 2026 Philippe Kevorkian. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philippe Kevorkian
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Pow
/-!

# Schwarzschild's incompressible fluid sphere and its junction with the exterior solution

Junction of Schwarzschild's incompressible fluid sphere with the exterior Schwarzschild metric.

## i. Overview

In his second 1916 paper, Schwarzschild solved Einstein's equations for a static sphere of
incompressible fluid of constant density `ρ₀`. The interior space is a portion of a
three-sphere of curvature radius `Rc`, with `Rc ^ 2 = 3 / (κ ρ₀)` (`κ = 8 π G`, `c = 1`),
and the surface of the fluid sits at the polar angle `χ_a` with `sin χ_a = Ra / Rc`, where
`Ra` is the areal radius of the surface. In the areal radius `r = Rc sin χ` the interior metric
coefficients are

- `g_tt = ((3 cos χ_a - cos χ) / 2) ^ 2 = (3 / 2 cos χ_a - 1 / 2 √(1 - r ^ 2 / Rc ^ 2)) ^ 2`,
- `g_rr = 1 / (1 - r ^ 2 / Rc ^ 2)`,

while outside the sphere the metric is the exterior Schwarzschild solution with
`g_tt = 1 - α / r`, `g_rr = 1 / (1 - α / r)` and `α = Ra ^ 3 / Rc ^ 2`. The pressure is
`ρ₀ + p = ρ₀ 2 cos χ_a / (3 cos χ_a - cos χ)`.

This file takes the two metrics and the pressure as given (the field equations are not
verified here) and proves the elementary properties of the junction at `r = Ra`: continuity
of `g_tt` and `g_rr`, differentiability of the glued `g_tt`, non-differentiability of the glued
`g_rr` in the curvature coordinate `r`, the vanishing of the pressure at the surface, and the
Schwarzschild bound `cos χ_a > 1 / 3` (equivalently `Ra > 9 / 8 α`) for the central pressure to
be positive.

## ii. Key results

- `IncompressibleSphere` contains the input data: `Rc`, `Ra`, `ρ₀` with `0 < Ra < Rc` and
  `0 < ρ₀`.
- `rs_div_Ra`: Schwarzschild's relation (40), `α / Ra = sin χ_a ^ 2`.
- `pressure_chia`: the pressure vanishes at the surface.
- `pressure_zero_pos_iff`: the central pressure is positive if and only if `cos χ_a > 1 / 3`.
- `one_third_lt_cosChia_iff_rs`: `cos χ_a > 1 / 3` if and only if `9 / 8 α < Ra`.
- `gttIn_Ra`, `grrIn_Ra`: the interior and exterior formulas agree at `r = Ra`.
- `gttGlue_hasDerivAt`: the glued `g_tt` is differentiable at `Ra` with derivative `Ra / Rc ^ 2`.
- `grrGlue_not_differentiableAt`: the glued `g_rr` is continuous but not differentiable at
  `Ra` (one-sided derivatives `2 Ra / (Rc ^ 2 cos χ_a ^ 4)` and `- Ra / (Rc ^ 2 cos χ_a ^ 4)`).

## iii. Table of contents

- A. The input data
- B. The Schwarzschild radius and the angle of the surface
- C. The pressure
  - C.1. Pressure at the surface and at the centre
  - C.2. The bound `cos χ_a > 1 / 3`
- D. The metric coefficients
  - D.1. The interior metric in the angle `χ`
  - D.2. The values at the surface agree
- E. Derivatives of the metric coefficients at the surface
  - E.1. Two auxiliary derivatives
  - E.2. Derivatives of `g_tt`
  - E.3. Derivatives of `g_rr`
- F. The glued metric coefficients
- G. Consequences for the junction
- H. A numerical instance

## iv. References

- K. Schwarzschild, "Uber das Gravitationsfeld einer Kugel aus inkompressibler Flussigkeit nach
  der Einsteinschen Theorie", Sitzungsberichte der Koniglich Preussischen Akademie der
  Wissenschaften (1916), 424-434. English translation by S. Antoci, arXiv:physics/9912033.
  Equations (28), (29), (30), (35), (36), (39), (40) and the discussion on pages 8-9 of the
  translation (pressure diverging at `cos χ_a = 1 / 3`, limit `9 / 8 α`).
- A. Lichnerowicz, "Theories relativistes de la gravitation et de l'electromagnetisme",
  Masson (1955), chapter III, sections 27-29 (junction conditions).

-/

@[expose] public section

noncomputable section

namespace GeneralRelativity

open Real

/-!

## A. The input data

The sphere is specified by the curvature radius `Rc` of the interior space, the areal radius
`Ra` of its surface and the constant density `ρ₀`. The sphere is a proper part of the spherical
space (`Ra < Rc`, so that `χ_a < π / 2`).

-/

/-- Schwarzschild's incompressible fluid sphere: the curvature radius `Rc` of the interior
  spherical space (`Rc ^ 2 = 3 / (κ ρ₀)`, Schwarzschild (37)), the areal radius `Ra` of the
  surface (Schwarzschild's `P_o`, (39)) and the constant density `ρ₀`, with `0 < Ra < Rc` and
  `0 < ρ₀`. -/
structure IncompressibleSphere where
  /-- The curvature radius of the interior spherical space. -/
  Rc : ℝ
  /-- The areal radius of the surface of the fluid. -/
  Ra : ℝ
  /-- The constant density of the fluid. -/
  ρ₀ : ℝ
  /-- The curvature radius is positive. -/
  Rc_pos : 0 < Rc
  /-- The radius of the surface is positive. -/
  Ra_pos : 0 < Ra
  /-- The sphere is a proper part of the spherical space. -/
  Ra_lt_Rc : Ra < Rc
  /-- The density is positive. -/
  ρ₀_pos : 0 < ρ₀

namespace IncompressibleSphere

variable (S : IncompressibleSphere)

/-!

## B. The Schwarzschild radius and the angle of the surface

-/

/-- The Schwarzschild radius `α = (κ ρ₀ / 3) P_o ^ 3 = Ra ^ 3 / Rc ^ 2` of the sphere,
  Schwarzschild (40). -/
def rs : ℝ := S.Ra ^ 3 / S.Rc ^ 2

/-- The polar angle `χ_a` of the surface, `sin χ_a = Ra / Rc`, Schwarzschild (28). -/
def chia : ℝ := Real.arcsin (S.Ra / S.Rc)

/-- The cosine of the angle of the surface, written as `√(1 - Ra ^ 2 / Rc ^ 2)`. -/
def cosChia : ℝ := √(1 - S.Ra ^ 2 / S.Rc ^ 2)

lemma one_sub_sq_div_sq_pos : 0 < 1 - S.Ra ^ 2 / S.Rc ^ 2 := by
  have h2 : 0 < S.Rc ^ 2 := pow_pos S.Rc_pos 2
  have h3 : S.Ra ^ 2 < S.Rc ^ 2 := by nlinarith [S.Ra_pos, S.Ra_lt_Rc, S.Rc_pos]
  rw [sub_pos, div_lt_one h2]
  exact h3

lemma cosChia_sq : S.cosChia ^ 2 = 1 - S.Ra ^ 2 / S.Rc ^ 2 := by
  unfold cosChia
  exact Real.sq_sqrt S.one_sub_sq_div_sq_pos.le

/-- `cosChia` is the cosine of `chia`. -/
lemma cosChia_eq_cos_chia : S.cosChia = Real.cos S.chia := by
  unfold cosChia chia
  rw [Real.cos_arcsin, div_pow]

lemma cosChia_pos : 0 < S.cosChia := by
  unfold cosChia
  exact Real.sqrt_pos.mpr S.one_sub_sq_div_sq_pos

lemma cosChia_lt_one : S.cosChia < 1 := by
  unfold cosChia
  rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)]
  have : 0 < S.Ra ^ 2 / S.Rc ^ 2 := div_pos (pow_pos S.Ra_pos 2) (pow_pos S.Rc_pos 2)
  linarith

/-- Schwarzschild (40): `α / P_o = sin χ_a ^ 2`. -/
lemma rs_div_Ra : S.rs / S.Ra = Real.sin S.chia ^ 2 := by
  unfold rs chia
  have h1 : -1 ≤ S.Ra / S.Rc := by
    have := div_pos S.Ra_pos S.Rc_pos
    linarith
  have h2 : S.Ra / S.Rc ≤ 1 := by
    rw [div_le_one S.Rc_pos]
    exact S.Ra_lt_Rc.le
  have hRa := S.Ra_pos.ne'
  have hRc := S.Rc_pos.ne'
  rw [Real.sin_arcsin h1 h2, div_pow]
  field_simp

/-- The surface of the sphere lies outside its Schwarzschild radius. -/
lemma rs_lt_Ra : S.rs < S.Ra := by
  unfold rs
  rw [div_lt_iff₀ (pow_pos S.Rc_pos 2)]
  have h3 : S.Ra ^ 2 < S.Rc ^ 2 := by nlinarith [S.Ra_pos, S.Ra_lt_Rc, S.Rc_pos]
  nlinarith [mul_lt_mul_of_pos_left h3 S.Ra_pos]

/-!

## C. The pressure

-/

/-- The pressure of the fluid at the polar angle `χ`, Schwarzschild (30):
  `ρ₀ + p = ρ₀ 2 cos χ_a / (3 cos χ_a - cos χ)`. -/
def pressure (χ : ℝ) : ℝ :=
  S.ρ₀ * (2 * S.cosChia / (3 * S.cosChia - Real.cos χ)) - S.ρ₀

/-!

### C.1. Pressure at the surface and at the centre

-/

/-- The pressure vanishes at the surface of the fluid. -/
lemma pressure_chia : S.pressure S.chia = 0 := by
  unfold pressure
  rw [← S.cosChia_eq_cos_chia]
  have hc : S.cosChia ≠ 0 := S.cosChia_pos.ne'
  rw [show 3 * S.cosChia - S.cosChia = 2 * S.cosChia by ring,
    div_self (mul_ne_zero two_ne_zero hc)]
  ring

/-- The pressure at the centre, away from the critical value `cos χ_a = 1 / 3`. -/
lemma pressure_zero (h : 3 * S.cosChia ≠ 1) :
    S.pressure 0 = S.ρ₀ * (1 - S.cosChia) / (3 * S.cosChia - 1) := by
  unfold pressure
  rw [Real.cos_zero]
  have h' : 3 * S.cosChia - 1 ≠ 0 := sub_ne_zero.mpr h
  rw [mul_div_assoc', eq_div_iff h', sub_mul, div_mul_cancel₀ _ h']
  ring

lemma pressure_zero_pos (hsub : 1 / 3 < S.cosChia) : 0 < S.pressure 0 := by
  have h : 3 * S.cosChia ≠ 1 := by
    intro h
    linarith
  rw [S.pressure_zero h]
  have h1 := S.cosChia_lt_one
  apply div_pos
  · apply mul_pos S.ρ₀_pos
    linarith
  · linarith

/-- The central pressure is positive if and only if `cos χ_a > 1 / 3`. For `cos χ_a < 1 / 3`
  the formula (30) is negative at the centre; at `cos χ_a = 1 / 3` the division by zero of
  Lean gives `pressure 0 = - ρ₀`. The divergence of the pressure at the critical value is not
  a statement of this file. -/
lemma pressure_zero_pos_iff : 0 < S.pressure 0 ↔ 1 / 3 < S.cosChia := by
  constructor
  · intro hp
    by_contra hle
    have hle' : S.cosChia ≤ 1 / 3 := not_lt.mp hle
    have hc := S.cosChia_pos
    have hρ := S.ρ₀_pos
    unfold pressure at hp
    rw [Real.cos_zero] at hp
    rcases lt_or_eq_of_le hle' with h | h
    · have hd : 3 * S.cosChia - 1 < 0 := by linarith
      have hq : 2 * S.cosChia / (3 * S.cosChia - 1) < 0 :=
        div_neg_of_pos_of_neg (by linarith) hd
      have := mul_neg_of_pos_of_neg hρ hq
      linarith
    · have hd : 3 * S.cosChia - 1 = 0 := by linarith
      rw [hd, div_zero, mul_zero] at hp
      linarith
  · intro h
    exact S.pressure_zero_pos h

/-!

### C.2. The bound `cos χ_a > 1 / 3`

Schwarzschild, page 9 of the translation: the pressure at the centre stays finite as long as
`Ra > 9 / 8 α`.

-/

lemma one_third_lt_cosChia_iff_sq : 1 / 3 < S.cosChia ↔ S.Ra ^ 2 < 8 / 9 * S.Rc ^ 2 := by
  unfold cosChia
  rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 3)]
  have h2 : 0 < S.Rc ^ 2 := pow_pos S.Rc_pos 2
  have hRc := S.Rc_pos.ne'
  have key : 1 - S.Ra ^ 2 / S.Rc ^ 2 = (S.Rc ^ 2 - S.Ra ^ 2) / S.Rc ^ 2 := by
    field_simp
  rw [key, lt_div_iff₀ h2]
  constructor <;> intro h <;> linarith

/-- `cos χ_a > 1 / 3` if and only if `Ra < √(8 / 9) Rc`. -/
lemma one_third_lt_cosChia_iff_Ra_lt : 1 / 3 < S.cosChia ↔ S.Ra < √(8 / 9) * S.Rc := by
  rw [S.one_third_lt_cosChia_iff_sq]
  have h : √(8 / 9) * S.Rc = √(8 / 9 * S.Rc ^ 2) := by
    rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq S.Rc_pos.le]
  rw [h, Real.lt_sqrt S.Ra_pos.le]

/-- `cos χ_a > 1 / 3` if and only if `9 / 8 α < Ra` (Schwarzschild, page 9). -/
lemma one_third_lt_cosChia_iff_rs : 1 / 3 < S.cosChia ↔ 9 / 8 * S.rs < S.Ra := by
  rw [S.one_third_lt_cosChia_iff_sq]
  unfold rs
  have h2 : 0 < S.Rc ^ 2 := pow_pos S.Rc_pos 2
  have hRa := S.Ra_pos
  rw [mul_div_assoc', div_lt_iff₀ h2]
  constructor
  · intro h
    nlinarith
  · intro h
    have h1 : S.Ra * (9 / 8 * S.Ra ^ 2) < S.Ra * S.Rc ^ 2 := by linarith
    have := lt_of_mul_lt_mul_left h1 hRa.le
    linarith

/-- At the critical value `cos χ_a = 1 / 3` the ratio `Ra / Rc = sin χ_a` (Schwarzschild's
  fall velocity, (42)) equals `√(8 / 9)`. -/
lemma Ra_div_Rc_of_cosChia_eq (hc : S.cosChia = 1 / 3) : S.Ra / S.Rc = √(8 / 9) := by
  have h1 : (S.Ra / S.Rc) ^ 2 = 8 / 9 := by
    have h2 := S.cosChia_sq
    rw [hc] at h2
    rw [div_pow]
    linarith
  rw [← h1, Real.sqrt_sq (div_pos S.Ra_pos S.Rc_pos).le]

/-!

## D. The metric coefficients

The interior metric (35) is written in the areal radius `r = Rc sin χ`; the relation with the
form in `χ` is a lemma (`gttIn_Rc_mul_sin`, `grrIn_Rc_mul_sin`), not a definition. The metric
coefficients are taken up to the sign of the signature.

-/

/-- The interior coefficient `g_tt` in the areal radius `r`, Schwarzschild (35):
  `(3 / 2 cos χ_a - 1 / 2 √(1 - r ^ 2 / Rc ^ 2)) ^ 2`. -/
def gttIn (r : ℝ) : ℝ :=
  (3 / 2 * S.cosChia - 1 / 2 * √(1 - r ^ 2 / S.Rc ^ 2)) ^ 2

/-- The interior coefficient `g_rr` in the areal radius `r`, Schwarzschild (35):
  `1 / (1 - r ^ 2 / Rc ^ 2)`. -/
def grrIn (r : ℝ) : ℝ := 1 / (1 - r ^ 2 / S.Rc ^ 2)

/-- The exterior coefficient `g_tt = 1 - α / r`, Schwarzschild (36). -/
def gttOut (r : ℝ) : ℝ := 1 - S.rs / r

/-- The exterior coefficient `g_rr = 1 / (1 - α / r)`, Schwarzschild (36). -/
def grrOut (r : ℝ) : ℝ := 1 / (1 - S.rs / r)

/-!

### D.1. The interior metric in the angle `χ`

-/

lemma one_sub_sin_sq (χ : ℝ) :
    1 - (S.Rc * Real.sin χ) ^ 2 / S.Rc ^ 2 = Real.cos χ ^ 2 := by
  rw [mul_pow, mul_div_cancel_left₀ _ (pow_ne_zero 2 S.Rc_pos.ne')]
  linarith [Real.sin_sq_add_cos_sq χ]

/-- Schwarzschild (35): in the angle `χ`, `g_tt = ((3 cos χ_a - cos χ) / 2) ^ 2`. -/
lemma gttIn_Rc_mul_sin {χ : ℝ} (h0 : 0 ≤ χ) (hπ : χ ≤ π / 2) :
    S.gttIn (S.Rc * Real.sin χ) = ((3 * S.cosChia - Real.cos χ) / 2) ^ 2 := by
  unfold gttIn
  rw [S.one_sub_sin_sq,
    Real.sqrt_sq (Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hπ⟩)]
  ring

/-- Schwarzschild (35): in the angle `χ`, the coefficient of `dχ ^ 2` is `Rc ^ 2`. -/
lemma grrIn_Rc_mul_sin {χ : ℝ} (hc : Real.cos χ ≠ 0) :
    S.grrIn (S.Rc * Real.sin χ) * (S.Rc * Real.cos χ) ^ 2 = S.Rc ^ 2 := by
  unfold grrIn
  rw [S.one_sub_sin_sq]
  field_simp

/-!

### D.2. The values at the surface agree

-/

/-- The interior and exterior formulas for `g_tt` take the same value at `r = Ra`. -/
lemma gttIn_Ra : S.gttIn S.Ra = S.gttOut S.Ra := by
  have hca : √(1 - S.Ra ^ 2 / S.Rc ^ 2) = S.cosChia := rfl
  unfold gttIn gttOut rs
  rw [hca, show (3 / 2 * S.cosChia - 1 / 2 * S.cosChia) ^ 2 = S.cosChia ^ 2 by ring,
    S.cosChia_sq]
  have hRa := S.Ra_pos.ne'
  have hRc := S.Rc_pos.ne'
  field_simp

/-- The interior and exterior formulas for `g_rr` take the same value at `r = Ra`. -/
lemma grrIn_Ra : S.grrIn S.Ra = S.grrOut S.Ra := by
  unfold grrIn grrOut rs
  congr 1
  have hRa := S.Ra_pos.ne'
  have hRc := S.Rc_pos.ne'
  field_simp

/-- The exterior form of `g_tt` at the surface determines the Schwarzschild radius: if
  `g_tt (Ra) = 1 - a / Ra` then `a = α = Ra ^ 3 / Rc ^ 2`, which is Schwarzschild (40). -/
lemma eq_rs_of_gttIn_Ra {a : ℝ} (h : S.gttIn S.Ra = 1 - a / S.Ra) : a = S.rs := by
  have h1 := S.gttIn_Ra
  rw [h] at h1
  unfold gttOut at h1
  have h2 : a / S.Ra = S.rs / S.Ra := by linarith
  rwa [div_left_inj' S.Ra_pos.ne'] at h2

/-- At the critical value `cos χ_a = 1 / 3`, `g_tt` vanishes at the centre. -/
lemma gttIn_zero_of_cosChia_eq (hcrit : S.cosChia = 1 / 3) : S.gttIn 0 = 0 := by
  unfold gttIn
  rw [hcrit]
  norm_num

/-!

## E. Derivatives of the metric coefficients at the surface

-/

/-!

### E.1. Two auxiliary derivatives

-/

lemma hasDerivAt_one_sub_sq_div (Rc r : ℝ) :
    HasDerivAt (fun x : ℝ => 1 - x ^ 2 / Rc ^ 2) (-(2 * r) / Rc ^ 2) r := by
  have h := ((hasDerivAt_pow 2 r).div_const (Rc ^ 2)).const_sub (1 : ℝ)
  exact h.congr_deriv (by rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one]; push_cast; ring)

lemma hasDerivAt_sqrt_one_sub_sq_div {Rc r : ℝ} (hu : 0 < 1 - r ^ 2 / Rc ^ 2) :
    HasDerivAt (fun x : ℝ => √(1 - x ^ 2 / Rc ^ 2))
      (-r / (Rc ^ 2 * √(1 - r ^ 2 / Rc ^ 2))) r := by
  have h : HasDerivAt (fun x : ℝ => √(1 - x ^ 2 / Rc ^ 2))
      (1 / (2 * √(1 - r ^ 2 / Rc ^ 2)) * (-(2 * r) / Rc ^ 2)) r :=
    (Real.hasDerivAt_sqrt hu.ne').comp r (hasDerivAt_one_sub_sq_div Rc r)
  have hs : √(1 - r ^ 2 / Rc ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hu).ne'
  refine h.congr_deriv ?_
  field_simp

/-!

### E.2. Derivatives of `g_tt`

-/

/-- The interior `g_tt` is differentiable at `Ra` with derivative `Ra / Rc ^ 2`. -/
lemma gttIn_hasDerivAt : HasDerivAt S.gttIn (S.Ra / S.Rc ^ 2) S.Ra := by
  have hu : 0 < 1 - S.Ra ^ 2 / S.Rc ^ 2 := S.one_sub_sq_div_sq_pos
  have hca : √(1 - S.Ra ^ 2 / S.Rc ^ 2) = S.cosChia := rfl
  have hc : S.cosChia ≠ 0 := S.cosChia_pos.ne'
  have hRc := S.Rc_pos.ne'
  have h : HasDerivAt
      (fun x : ℝ => (3 / 2 * S.cosChia - 1 / 2 * √(1 - x ^ 2 / S.Rc ^ 2)) ^ 2)
      ((2 : ℕ) * (3 / 2 * S.cosChia - 1 / 2 * √(1 - S.Ra ^ 2 / S.Rc ^ 2)) ^ (2 - 1)
        * (-(1 / 2 * (-S.Ra / (S.Rc ^ 2 * √(1 - S.Ra ^ 2 / S.Rc ^ 2)))))) S.Ra :=
    (((hasDerivAt_sqrt_one_sub_sq_div hu).const_mul (1 / 2 : ℝ)).const_sub
      (3 / 2 * S.cosChia)).pow 2
  rw [show S.gttIn
      = fun x : ℝ => (3 / 2 * S.cosChia - 1 / 2 * √(1 - x ^ 2 / S.Rc ^ 2)) ^ 2 from rfl]
  refine h.congr_deriv ?_
  rw [hca, show (2 : ℕ) - 1 = 1 from rfl, pow_one]
  push_cast
  field_simp
  ring

/-- The derivative of the interior `g_tt` at `Ra` is `Ra / Rc ^ 2`. -/
lemma deriv_gttIn_Ra : deriv S.gttIn S.Ra = S.Ra / S.Rc ^ 2 :=
  S.gttIn_hasDerivAt.deriv

/-- The exterior `g_tt` is differentiable at `Ra` with derivative `α / Ra ^ 2 = Ra / Rc ^ 2`. -/
lemma gttOut_hasDerivAt : HasDerivAt S.gttOut (S.Ra / S.Rc ^ 2) S.Ra := by
  have hf : S.gttOut = fun x : ℝ => 1 - S.rs * x⁻¹ := by
    funext x
    simp [gttOut, div_eq_mul_inv]
  have h := ((hasDerivAt_inv S.Ra_pos.ne').const_mul S.rs).const_sub (1 : ℝ)
  rw [hf]
  refine h.congr_deriv ?_
  unfold rs
  have hRa := S.Ra_pos.ne'
  have hRc := S.Rc_pos.ne'
  field_simp

/-- The derivative of the exterior `g_tt` at `Ra` is `Ra / Rc ^ 2`. -/
lemma deriv_gttOut_Ra : deriv S.gttOut S.Ra = S.Ra / S.Rc ^ 2 :=
  S.gttOut_hasDerivAt.deriv

/-- The derivatives of the two formulas for `g_tt` agree at `r = Ra`. -/
lemma deriv_gttIn_Ra_eq_deriv_gttOut_Ra : deriv S.gttIn S.Ra = deriv S.gttOut S.Ra := by
  rw [S.deriv_gttIn_Ra, S.deriv_gttOut_Ra]

/-!

### E.3. Derivatives of `g_rr`

-/

/-- The interior `g_rr` is differentiable at `Ra` with derivative
  `2 Ra / (Rc ^ 2 cos χ_a ^ 4)`. -/
lemma grrIn_hasDerivAt :
    HasDerivAt S.grrIn (2 * S.Ra / (S.Rc ^ 2 * S.cosChia ^ 4)) S.Ra := by
  have hu : 1 - S.Ra ^ 2 / S.Rc ^ 2 ≠ 0 := S.one_sub_sq_div_sq_pos.ne'
  have hf : S.grrIn = fun x : ℝ => (1 - x ^ 2 / S.Rc ^ 2)⁻¹ := by
    funext x
    simp [grrIn]
  have h : HasDerivAt (fun x : ℝ => (1 - x ^ 2 / S.Rc ^ 2)⁻¹)
      (-(-(2 * S.Ra) / S.Rc ^ 2) / (1 - S.Ra ^ 2 / S.Rc ^ 2) ^ 2) S.Ra :=
    (hasDerivAt_one_sub_sq_div S.Rc S.Ra).inv hu
  rw [hf]
  refine h.congr_deriv ?_
  rw [show S.cosChia ^ 4 = (S.cosChia ^ 2) ^ 2 by ring, S.cosChia_sq]
  have hRc := S.Rc_pos.ne'
  field_simp

/-- The derivative of the interior `g_rr` at `Ra`. -/
lemma deriv_grrIn_Ra : deriv S.grrIn S.Ra = 2 * S.Ra / (S.Rc ^ 2 * S.cosChia ^ 4) :=
  S.grrIn_hasDerivAt.deriv

/-- The exterior `g_rr` is differentiable at `Ra` with derivative
  `- Ra / (Rc ^ 2 cos χ_a ^ 4)`. -/
lemma grrOut_hasDerivAt :
    HasDerivAt S.grrOut (-(S.Ra / (S.Rc ^ 2 * S.cosChia ^ 4))) S.Ra := by
  have hRa := S.Ra_pos.ne'
  have hRc := S.Rc_pos.ne'
  have hf : S.grrOut = fun x : ℝ => (1 - S.rs * x⁻¹)⁻¹ := by
    funext x
    simp [grrOut, div_eq_mul_inv]
  have hv : 1 - S.rs * S.Ra⁻¹ ≠ 0 := by
    have : 1 - S.rs * S.Ra⁻¹ = 1 - S.Ra ^ 2 / S.Rc ^ 2 := by
      unfold rs
      field_simp
    rw [this]
    exact S.one_sub_sq_div_sq_pos.ne'
  have h : HasDerivAt (fun x : ℝ => (1 - S.rs * x⁻¹)⁻¹)
      (-(-(S.rs * -(S.Ra ^ 2)⁻¹)) / (1 - S.rs * S.Ra⁻¹) ^ 2) S.Ra :=
    (((hasDerivAt_inv hRa).const_mul S.rs).const_sub (1 : ℝ)).inv hv
  rw [hf]
  refine h.congr_deriv ?_
  rw [show S.cosChia ^ 4 = (S.cosChia ^ 2) ^ 2 by ring, S.cosChia_sq]
  unfold rs
  field_simp

/-- The derivative of the exterior `g_rr` at `Ra`. -/
lemma deriv_grrOut_Ra : deriv S.grrOut S.Ra = -(S.Ra / (S.Rc ^ 2 * S.cosChia ^ 4)) :=
  S.grrOut_hasDerivAt.deriv

/-- The derivatives of the two formulas for `g_rr` differ at `r = Ra`, in the curvature
  coordinate `r`. -/
lemma deriv_grrIn_Ra_ne_deriv_grrOut_Ra : deriv S.grrIn S.Ra ≠ deriv S.grrOut S.Ra := by
  rw [S.deriv_grrIn_Ra, S.deriv_grrOut_Ra]
  have hc := S.cosChia_pos
  have hRa := S.Ra_pos
  have hd : 0 < S.Rc ^ 2 * S.cosChia ^ 4 := mul_pos (pow_pos S.Rc_pos 2) (pow_pos hc 4)
  have h1 : 0 < 2 * S.Ra / (S.Rc ^ 2 * S.cosChia ^ 4) := div_pos (by linarith) hd
  have h2 : 0 < S.Ra / (S.Rc ^ 2 * S.cosChia ^ 4) := div_pos hRa hd
  intro h
  linarith

/-!

## F. The glued metric coefficients

The glued coefficients use the interior formula for `r ≤ Ra` and the exterior formula
beyond. The glued `g_tt` is differentiable at `Ra`; the glued `g_rr` is continuous but not
differentiable at `Ra`, since its one-sided derivatives differ.

-/

/-- The glued `g_tt`: interior formula for `r ≤ Ra`, exterior formula beyond. -/
def gttGlue (r : ℝ) : ℝ := if r ≤ S.Ra then S.gttIn r else S.gttOut r

/-- The glued `g_rr`: interior formula for `r ≤ Ra`, exterior formula beyond. -/
def grrGlue (r : ℝ) : ℝ := if r ≤ S.Ra then S.grrIn r else S.grrOut r

/-- The glued `g_tt` is differentiable at `Ra` with derivative `Ra / Rc ^ 2`. -/
lemma gttGlue_hasDerivAt : HasDerivAt S.gttGlue (S.Ra / S.Rc ^ 2) S.Ra := by
  have hle : HasDerivWithinAt S.gttGlue (S.Ra / S.Rc ^ 2) (Set.Iic S.Ra) S.Ra := by
    refine S.gttIn_hasDerivAt.hasDerivWithinAt.congr ?_ ?_
    · intro x hx
      simp [gttGlue, Set.mem_Iic.mp hx]
    · simp [gttGlue]
  have hge : HasDerivWithinAt S.gttGlue (S.Ra / S.Rc ^ 2) (Set.Ici S.Ra) S.Ra := by
    refine S.gttOut_hasDerivAt.hasDerivWithinAt.congr ?_ ?_
    · intro x hx
      rcases eq_or_lt_of_le (Set.mem_Ici.mp hx) with h | h
      · rw [← h]
        simp [gttGlue, S.gttIn_Ra]
      · simp [gttGlue, not_le.mpr h]
    · simp [gttGlue, S.gttIn_Ra]
  have h := hle.union hge
  rwa [Set.Iic_union_Ici, hasDerivWithinAt_univ] at h

/-- The glued `g_tt` is continuous at `Ra`. -/
lemma gttGlue_continuousAt : ContinuousAt S.gttGlue S.Ra :=
  S.gttGlue_hasDerivAt.continuousAt

/-- The left derivative of the glued `g_rr` at `Ra` (interior formula). -/
lemma grrGlue_hasDerivWithinAt_Iic :
    HasDerivWithinAt S.grrGlue (2 * S.Ra / (S.Rc ^ 2 * S.cosChia ^ 4)) (Set.Iic S.Ra) S.Ra := by
  refine S.grrIn_hasDerivAt.hasDerivWithinAt.congr ?_ ?_
  · intro x hx
    simp [grrGlue, Set.mem_Iic.mp hx]
  · simp [grrGlue]

/-- The right derivative of the glued `g_rr` at `Ra` (exterior formula). -/
lemma grrGlue_hasDerivWithinAt_Ici :
    HasDerivWithinAt S.grrGlue (-(S.Ra / (S.Rc ^ 2 * S.cosChia ^ 4))) (Set.Ici S.Ra) S.Ra := by
  refine S.grrOut_hasDerivAt.hasDerivWithinAt.congr ?_ ?_
  · intro x hx
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hx) with h | h
    · rw [← h]
      simp [grrGlue, S.grrIn_Ra]
    · simp [grrGlue, not_le.mpr h]
  · simp [grrGlue, S.grrIn_Ra]

/-- The glued `g_rr` is continuous at `Ra`. -/
lemma grrGlue_continuousAt : ContinuousAt S.grrGlue S.Ra := by
  have h := S.grrGlue_hasDerivWithinAt_Iic.continuousWithinAt.union
    S.grrGlue_hasDerivWithinAt_Ici.continuousWithinAt
  rwa [Set.Iic_union_Ici, continuousWithinAt_univ] at h

/-- The glued `g_rr` is not differentiable at `Ra`: its left and right derivatives, unique on
  `Iic Ra` and `Ici Ra`, differ. -/
lemma grrGlue_not_differentiableAt : ¬ DifferentiableAt ℝ S.grrGlue S.Ra := by
  intro hd
  have hdw1 : HasDerivWithinAt S.grrGlue (deriv S.grrGlue S.Ra) (Set.Iic S.Ra) S.Ra :=
    hd.hasDerivAt.hasDerivWithinAt
  have hdw2 : HasDerivWithinAt S.grrGlue (deriv S.grrGlue S.Ra) (Set.Ici S.Ra) S.Ra :=
    hd.hasDerivAt.hasDerivWithinAt
  have h1 := UniqueDiffWithinAt.eq_deriv _ (uniqueDiffWithinAt_Iic S.Ra)
    S.grrGlue_hasDerivWithinAt_Iic hdw1
  have h2 := UniqueDiffWithinAt.eq_deriv _ (uniqueDiffWithinAt_Ici S.Ra)
    S.grrGlue_hasDerivWithinAt_Ici hdw2
  have hc := S.cosChia_pos
  have hRa := S.Ra_pos
  have hD : 0 < S.Rc ^ 2 * S.cosChia ^ 4 := mul_pos (pow_pos S.Rc_pos 2) (pow_pos hc 4)
  have hp1 : 0 < 2 * S.Ra / (S.Rc ^ 2 * S.cosChia ^ 4) := div_pos (by linarith) hD
  have hp2 : 0 < S.Ra / (S.Rc ^ 2 * S.cosChia ^ 4) := div_pos hRa hD
  linarith

/-!

## G. Consequences for the junction

In a Gaussian coordinate `l` along the radius, `dr / dl = 1 / √g_rr` and
`d g_tt / dl = g_tt' / √g_rr`. Both quantities take the same value at `Ra` from the two
formulas (Lichnerowicz, chapter III, section 28, evaluated at the surface). The coordinate `l`
itself is not constructed here.

-/

/-- `dr / dl = 1 / √g_rr` takes the same value at `Ra` from the two formulas. -/
lemma one_div_sqrt_grrIn_Ra : 1 / √(S.grrIn S.Ra) = 1 / √(S.grrOut S.Ra) := by
  rw [S.grrIn_Ra]

/-- `d g_tt / dl = g_tt' / √g_rr` takes the same value at `Ra` from the two formulas. -/
lemma deriv_gttIn_div_sqrt_grrIn_Ra :
    deriv S.gttIn S.Ra / √(S.grrIn S.Ra) = deriv S.gttOut S.Ra / √(S.grrOut S.Ra) := by
  rw [S.deriv_gttIn_Ra_eq_deriv_gttOut_Ra, S.grrIn_Ra]

/-!

## H. A numerical instance

The sphere with `Rc = 1`, `Ra = 3 / 5` and `ρ₀ = 1`: `cos χ_a = 4 / 5`, `α = 27 / 125`,
`9 / 8 α < Ra`, central pressure `1 / 7`.

-/

example : (⟨1, 3 / 5, 1, by norm_num, by norm_num, by norm_num, by norm_num⟩ :
    IncompressibleSphere).cosChia = 4 / 5 := by
  show √(1 - (3 / 5 : ℝ) ^ 2 / 1 ^ 2) = 4 / 5
  rw [show (1 : ℝ) - (3 / 5) ^ 2 / 1 ^ 2 = (4 / 5) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

example : (⟨1, 3 / 5, 1, by norm_num, by norm_num, by norm_num, by norm_num⟩ :
    IncompressibleSphere).rs = 27 / 125 := by
  show (3 / 5 : ℝ) ^ 3 / 1 ^ 2 = 27 / 125
  norm_num

example : 9 / 8 * (⟨1, 3 / 5, 1, by norm_num, by norm_num, by norm_num, by norm_num⟩ :
    IncompressibleSphere).rs < 3 / 5 := by
  show 9 / 8 * ((3 / 5 : ℝ) ^ 3 / 1 ^ 2) < 3 / 5
  norm_num

end IncompressibleSphere

end GeneralRelativity

end
