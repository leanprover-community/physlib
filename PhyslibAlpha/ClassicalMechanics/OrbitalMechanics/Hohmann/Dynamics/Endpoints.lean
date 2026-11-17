/-
Copyright (c) 2026 Chengyuan AI Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qianli Ma
-/
module

public import PhyslibAlpha.ClassicalMechanics.OrbitalMechanics.Hohmann.Dynamics.Dynamics

/-!
# Apsidal speeds on the Hohmann ellipse

The transfer velocity is tangential at both apses.

## i. Overview

Evaluating the actual time derivative at departure and arrival gives the periapsis and apoapsis
speeds. These speeds admit closed forms in the two orbital radii.

## ii. Key results

- `periSpeed_formula` gives the main result of this module.

## iii. Table of contents

- A. Positions and velocities at the apses

## iv. References

- [ref: hohmann_jpl_orbital_mechanics] describes the Hohmann ellipse and its apses.
-/

@[expose] public noncomputable section

namespace ClassicalMechanics.HohmannTransfer

/-!
## A. Positions and velocities at the apses
-/

/-- The transfer speed at periapsis. -/
def periSpeed (p : Parameters) : ℝ := p.b*p.n/(1-p.e)
/-- The transfer speed at apoapsis. -/
def apoSpeed (p : Parameters) : ℝ := p.b*p.n/(1+p.e)

lemma periSpeed_pos (p : Parameters) : 0 < periSpeed p :=
  div_pos (mul_pos p.b_pos p.n_pos) p.one_sub_e_pos
lemma apoSpeed_pos (p : Parameters) : 0 < apoSpeed p :=
  div_pos (mul_pos p.b_pos p.n_pos) p.one_add_e_pos
@[simp] lemma position_departure (p : Parameters) : position p 0 = pack p.r₁ 0 := by
  simp [position]
@[simp] lemma position_arrival (p : Parameters) :
    position p p.transferTime = pack (-p.r₂) 0 := by simp [position]
@[simp] lemma velocity_departure (p : Parameters) : velocity p 0 = pack 0 (periSpeed p) := by
  simp [velocity, velocityAtAnomaly, periSpeed]
@[simp] lemma velocity_arrival (p : Parameters) :
    velocity p p.transferTime = pack 0 (-apoSpeed p) := by
  apply Complex.ext
  · simp [velocity, velocityAtAnomaly]
  · simp [velocity, velocityAtAnomaly, apoSpeed]
    ring
lemma periSpeed_sq (p : Parameters) :
    periSpeed p ^ 2 = 2*p.mu*p.r₂/(p.r₁*(p.r₁+p.r₂)) := by
  have hper := p.a_mul_one_sub_e
  have haps := p.a_mul_one_add_e
  have hb := p.b_sq
  have hn := p.n_sq
  unfold periSpeed
  rw [div_pow, mul_pow, hb, hn]
  have he : 1-p.e = p.r₁/p.a := by
    apply (eq_div_iff p.a_ne).2
    nlinarith [hper]
  rw [he]
  unfold Parameters.a
  field_simp [p.r₁_ne, ne_of_gt p.sum_pos]

lemma apoSpeed_sq (p : Parameters) :
    apoSpeed p ^ 2 = 2*p.mu*p.r₁/(p.r₂*(p.r₁+p.r₂)) := by
  have haps := p.a_mul_one_add_e
  unfold apoSpeed
  rw [div_pow, mul_pow, p.b_sq, p.n_sq]
  have he : 1+p.e = p.r₂/p.a := by
    apply (eq_div_iff p.a_ne).2
    nlinarith [haps]
  rw [he]
  unfold Parameters.a
  field_simp [p.r₂_ne, ne_of_gt p.sum_pos]

lemma periSpeed_formula (p : Parameters) :
    periSpeed p = Real.sqrt (2*p.mu*p.r₂/(p.r₁*(p.r₁+p.r₂))) := by
  have hs := Real.sq_sqrt (le_of_lt
    (div_pos (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) p.mu_pos) p.r₂_pos)
      (mul_pos p.r₁_pos p.sum_pos)))
  have hn := Real.sqrt_nonneg (2*p.mu*p.r₂/(p.r₁*(p.r₁+p.r₂)))
  have hp := periSpeed_pos p
  have he := periSpeed_sq p
  nlinarith
lemma apoSpeed_formula (p : Parameters) :
    apoSpeed p = Real.sqrt (2*p.mu*p.r₁/(p.r₂*(p.r₁+p.r₂))) := by
  have hs := Real.sq_sqrt (le_of_lt
    (div_pos (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) p.mu_pos) p.r₁_pos)
      (mul_pos p.r₂_pos p.sum_pos)))
  have hn := Real.sqrt_nonneg (2*p.mu*p.r₁/(p.r₂*(p.r₁+p.r₂)))
  have hp := apoSpeed_pos p
  have he := apoSpeed_sq p
  nlinarith
lemma norm_velocity_departure (p : Parameters) : ‖velocity p 0‖ = periSpeed p := by
  rw [velocity_departure, norm_pack_vertical, abs_of_pos (periSpeed_pos p)]
lemma norm_velocity_arrival (p : Parameters) :
    ‖velocity p p.transferTime‖ = apoSpeed p := by
  rw [velocity_arrival, norm_pack_vertical, abs_neg, abs_of_pos (apoSpeed_pos p)]

end ClassicalMechanics.HohmannTransfer
