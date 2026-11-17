/-
Copyright (c) 2026 Chengyuan AI Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qianli Ma
-/
module

public import PhyslibAlpha.ClassicalMechanics.OrbitalMechanics.Hohmann.Dynamics.Differentiation

/-!
# Newtonian dynamics of the Hohmann ellipse

The transfer coast solves the inverse-square equation.

## i. Overview

The norm of the position stays positive. Rewriting the radial acceleration with the mean motion
law gives the Newtonian acceleration at every real time.

## ii. Key results

- `second_deriv_position` gives the main result of this module.

## iii. Table of contents

- A. The Newtonian equation and periodicity

## iv. References

- [ref: hohmann_jpl_orbital_mechanics] describes the Hohmann ellipse and its apses.
-/

@[expose] public noncomputable section

namespace ClassicalMechanics.HohmannTransfer

/-!
## A. The Newtonian equation and periodicity
-/

/-- The inverse-square central acceleration at the given position. -/
def gravity (mu : ℝ) (q : ℂ) : ℂ := -(mu/‖q‖^3) • q

lemma norm_position (p : Parameters) (t : ℝ) :
    ‖position p t‖ = radial p (anomaly p t) := norm_ellipse p _
lemma position_bounds (p : Parameters) (t : ℝ) :
    p.r₁ ≤ ‖position p t‖ ∧ ‖position p t‖ ≤ p.r₂ := by
  rw [norm_position]
  exact radial_bounds p _
lemma norm_position_pos (p : Parameters) (t : ℝ) : 0 < ‖position p t‖ := by
  rw [norm_position]
  exact radial_pos p _
lemma position_ne_zero (p : Parameters) (t : ℝ) : position p t ≠ 0 :=
  ellipse_ne_zero p _
lemma acceleration_coefficient (p : Parameters) (u : ℝ) :
    p.n^2/(D p u)^3 = p.mu/(radial p u)^3 := by
  rw [p.n_sq]
  unfold radial
  field_simp [p.a_ne, D_ne p u]
lemma hasDerivAt_velocity_newton (p : Parameters) (t : ℝ) :
    HasDerivAt (velocity p) (gravity p.mu (position p t)) t := by
  convert hasDerivAt_velocity p t using 1
  rw [gravity, norm_position, acceleration_coefficient]
lemma second_deriv_position (p : Parameters) (t : ℝ) :
    deriv (deriv (position p)) t = -(p.mu/‖position p t‖^3) • position p t := by
  rw [deriv_position]
  exact (hasDerivAt_velocity_newton p t).deriv
lemma position_periodic (p : Parameters) :
    Function.Periodic (position p) (2*p.transferTime) := by
  intro t
  unfold position
  rw [anomaly_add_period]
  exact ellipse_periodic p _
lemma velocity_periodic (p : Parameters) :
    Function.Periodic (velocity p) (2*p.transferTime) := by
  intro t
  unfold velocity
  rw [anomaly_add_period]
  apply Complex.ext <;>
    simp [velocityAtAnomaly, D, Real.sin_add_two_pi, Real.cos_add_two_pi]

end ClassicalMechanics.HohmannTransfer
