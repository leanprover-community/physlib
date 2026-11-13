/-
Copyright (c) 2026 Chengyuan AI Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chengyuan AI Lab
-/
module

public import PhyslibAlpha.ClassicalMechanics.OrbitalMechanics.Hohmann.Dynamics.Parameters
public import PhyslibAlpha.ClassicalMechanics.OrbitalMechanics.Hohmann.Dynamics.Plane

/-!
# Geometry of the Hohmann ellipse

The eccentric anomaly parameterizes the transfer ellipse.

## i. Overview

The attracting centre is at the origin. The distance from the focus lies between the two circular
radii, with equality at the two apses.

## ii. Key results

- `norm_ellipse` gives the main result of this module.

## iii. Table of contents

- A. The ellipse and its apses

## iv. References

- [ref: hohmann_jpl_orbital_mechanics] describes the Hohmann ellipse and its apses.
-/

@[expose] public noncomputable section

namespace ClassicalMechanics.HohmannTransfer

/-!
## A. The ellipse and its apses
-/

/-- The focus distance divided by the semimajor axis. -/
def D (p : Parameters) (u : ℝ) : ℝ := 1 - p.e * Real.cos u
/-- The distance from the attracting focus at a given eccentric anomaly. -/
def radial (p : Parameters) (u : ℝ) : ℝ := p.a * D p u
/-- The position on the transfer ellipse at the given eccentric anomaly. -/
def ellipse (p : Parameters) (u : ℝ) : ℂ :=
  pack (p.a * (Real.cos u - p.e)) (p.b * Real.sin u)
/-- The physical velocity on the transfer ellipse at the given anomaly. -/
def velocityAtAnomaly (p : Parameters) (u : ℝ) : ℂ :=
  pack (-p.a * p.n * Real.sin u / D p u)
    (p.b * p.n * Real.cos u / D p u)

lemma D_lower (p : Parameters) (u : ℝ) : 1 - p.e ≤ D p u := by
  unfold D
  nlinarith [Real.cos_le_one u, p.e_pos]
lemma D_upper (p : Parameters) (u : ℝ) : D p u ≤ 1 + p.e := by
  unfold D
  nlinarith [Real.neg_one_le_cos u, p.e_pos]
lemma D_pos (p : Parameters) (u : ℝ) : 0 < D p u :=
  lt_of_lt_of_le p.one_sub_e_pos (D_lower p u)
lemma D_ne (p : Parameters) (u : ℝ) : D p u ≠ 0 := ne_of_gt (D_pos p u)
lemma radial_pos (p : Parameters) (u : ℝ) : 0 < radial p u :=
  mul_pos p.a_pos (D_pos p u)
lemma ellipse_squared_radius (p : Parameters) (u : ℝ) :
    (ellipse p u).re ^ 2 + (ellipse p u).im ^ 2 = (radial p u)^2 := by
  have hb := p.b_sq_ellipse
  have ht := Real.sin_sq_add_cos_sq u
  simp only [ellipse, pack_re, pack_im, radial, D]
  calc
    (p.a * (Real.cos u - p.e)) ^ 2 + (p.b * Real.sin u) ^ 2 =
        p.a^2*(Real.cos u-p.e)^2 + p.b^2*Real.sin u^2 := by ring
    _ = (p.a * (1-p.e*Real.cos u))^2 := by
      rw [hb]
      nlinarith [congrArg (fun x : ℝ => p.a^2*(1-p.e^2)*x) ht]
lemma norm_ellipse (p : Parameters) (u : ℝ) : ‖ellipse p u‖ = radial p u := by
  apply norm_pack_eq (le_of_lt (radial_pos p u))
  exact ellipse_squared_radius p u
lemma radial_bounds (p : Parameters) (u : ℝ) :
    p.r₁ ≤ radial p u ∧ radial p u ≤ p.r₂ := by
  constructor
  · rw [← p.a_mul_one_sub_e]
    exact mul_le_mul_of_nonneg_left (D_lower p u) (le_of_lt p.a_pos)
  · rw [← p.a_mul_one_add_e]
    exact mul_le_mul_of_nonneg_left (D_upper p u) (le_of_lt p.a_pos)
lemma ellipse_ne_zero (p : Parameters) (u : ℝ) : ellipse p u ≠ 0 := by
  intro h
  have hn := norm_ellipse p u
  rw [h, norm_zero] at hn
  linarith [radial_pos p u]
@[simp] lemma D_zero (p : Parameters) : D p 0 = 1 - p.e := by simp [D]
@[simp] lemma D_pi (p : Parameters) : D p Real.pi = 1 + p.e := by simp [D]
@[simp] lemma ellipse_zero (p : Parameters) : ellipse p 0 = pack p.r₁ 0 := by
  apply Complex.ext <;> simp [ellipse]
  exact p.a_mul_one_sub_e
@[simp] lemma ellipse_pi (p : Parameters) : ellipse p Real.pi = pack (-p.r₂) 0 := by
  apply Complex.ext <;> simp [ellipse]
  nlinarith [p.a_mul_one_add_e]
lemma ellipse_periodic (p : Parameters) : Function.Periodic (ellipse p) (2*Real.pi) := by
  intro u
  apply Complex.ext <;> simp [ellipse, Real.cos_add_two_pi, Real.sin_add_two_pi]

end ClassicalMechanics.HohmannTransfer
