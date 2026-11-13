/-
Copyright (c) 2026 Qianli Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qianli Ma
-/
module

public import PhyslibAlpha.ClassicalMechanics.OrbitalMechanics.LagrangeThreeBody.Dynamics

/-!
# Period of the Lagrange orbit
The positions and velocities share a positive period fixed by the masses and side length.

## i. Overview

Uniform rotation advances by one full revolution in one period. The angular speed
determined by total mass and side length gives the period law.

## ii. Key results

- `kepler_period_law` gives the main result of this module.

## iii. Table of contents

- A. The period and half-period motion

## iv. References

Chenciner and Féjoz, [ref: chenciner_fejoz_2008], §8, gives the equilateral
reduction of the Newtonian equations for arbitrary masses.
The Lean construction is adapted from [ref: ma_lagrange_three_body_lean].
-/

@[expose] public noncomputable section
namespace ClassicalMechanics.LagrangeThreeBody

/-!
## A. The period and half-period motion
-/

lemma orbitPeriod_pos (p : Parameters) : 0 < orbitPeriod p := by
  exact div_pos (mul_pos (by norm_num) Real.pi_pos) (angularSpeed_pos p)

lemma angularSpeed_mul_period (p : Parameters) :
    angularSpeed p * orbitPeriod p = 2 * Real.pi := by
  unfold orbitPeriod
  field_simp [ne_of_gt (angularSpeed_pos p)]

lemma trajectory_periodic (p : Parameters) (i : Fin 3) :
    Function.Periodic (fun t => trajectory p t i) (orbitPeriod p) := by
  simpa only [trajectory_eq_rotate, orbitPeriod] using
    rotate_periodic (angularSpeed p) (ne_of_gt (angularSpeed_pos p)) (initialConfig p i)

lemma velocity_periodic (p : Parameters) (i : Fin 3) :
    Function.Periodic (fun t => velocity p t i) (orbitPeriod p) := by
  simpa only [velocity_eq_rotateVelocity, orbitPeriod] using
    rotateVelocity_periodic (angularSpeed p) (ne_of_gt (angularSpeed_pos p))
      (initialConfig p i)

lemma configuration_periodic (p : Parameters) :
    Function.Periodic (trajectory p) (orbitPeriod p) := by
  intro t
  funext i
  exact trajectory_periodic p i t

lemma phaseSpace_periodic (p : Parameters) :
    Function.Periodic (fun t => (trajectory p t, velocity p t)) (orbitPeriod p) := by
  intro t
  apply Prod.ext
  · exact configuration_periodic p t
  · funext i
    exact velocity_periodic p i t

/-- Period--size--mass law; all factors are explicit and positive where needed. -/
lemma kepler_period_law (p : Parameters) :
    orbitPeriod p ^ 2 * (p.G * totalMass p.mass) =
      4 * Real.pi ^ 2 * p.side ^ 3 := by
  have hs : p.side ^ 3 ≠ 0 := pow_ne_zero 3 (ne_of_gt p.side_pos)
  have hfreq : angularSpeed p ^ 2 * p.side ^ 3 = p.G * totalMass p.mass :=
    (eq_div_iff hs).mp (angularSpeed_sq p)
  calc
    orbitPeriod p ^ 2 * (p.G * totalMass p.mass) =
        orbitPeriod p ^ 2 * (angularSpeed p ^ 2 * p.side ^ 3) := by rw [hfreq]
    _ = (angularSpeed p * orbitPeriod p) ^ 2 * p.side ^ 3 := by ring
    _ = 4 * Real.pi ^ 2 * p.side ^ 3 := by rw [angularSpeed_mul_period]; ring

lemma orbitPeriod_sq (p : Parameters) :
    orbitPeriod p ^ 2 = 4 * Real.pi ^ 2 * p.side ^ 3 / (p.G * totalMass p.mass) := by
  apply (eq_div_iff (mul_ne_zero (ne_of_gt p.G_pos)
    (ne_of_gt (totalMass_pos p.mass p.mass_pos)))).mpr
  exact kepler_period_law p

lemma rotate_add_pi (θ : ℝ) (z : ℂ) : rotate (θ + Real.pi) z = -rotate θ z := by
  apply Complex.ext <;> simp [rotate, Real.sin_add, Real.cos_add] <;> ring

/-- After half a revolution, every position is the negative of its former value. -/
lemma trajectory_antipodal (p : Parameters) (t : ℝ) (i : Fin 3) :
    trajectory p (t + orbitPeriod p / 2) i = -trajectory p t i := by
  have hθ : angularSpeed p * (t + orbitPeriod p / 2) =
      angularSpeed p * t + Real.pi := by
    nlinarith [angularSpeed_mul_period p]
  rw [trajectory_eq_rotate, trajectory_eq_rotate, hθ, rotate_add_pi]

end ClassicalMechanics.LagrangeThreeBody
