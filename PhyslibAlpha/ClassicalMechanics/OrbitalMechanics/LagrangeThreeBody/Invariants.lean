/-
Copyright (c) 2026 Qianli Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qianli Ma
-/
module

public import PhyslibAlpha.ClassicalMechanics.OrbitalMechanics.LagrangeThreeBody.Existence

/-!
# Mechanical invariants of the Lagrange orbit
The moment of inertia, energy, and angular momentum have constant closed forms.

## i. Overview

The potential counts each unordered pair once. The velocity is tangent to uniform
rotation, so kinetic energy and angular momentum follow from the moment of inertia.

## ii. Key results

- `totalEnergy_formula` gives the main result of this module.

## iii. Table of contents

- A. Moment of inertia, energy, and angular momentum

## iv. References

Chenciner and Féjoz, [ref: chenciner_fejoz_2008], §8, gives the equilateral
reduction of the Newtonian equations for arbitrary masses.
The Lean construction is adapted from [ref: ma_lagrange_three_body_lean].
-/

@[expose] public noncomputable section
open scoped BigOperators
namespace ClassicalMechanics.LagrangeThreeBody

/-!
## A. Moment of inertia, energy, and angular momentum
-/

/-- Sum of the three pairwise mass products. -/
def pairMassSum (p : Parameters) : ℝ :=
  p.mass 0 * p.mass 1 + p.mass 0 * p.mass 2 + p.mass 1 * p.mass 2

/-- Moment of inertia around the barycentric origin. -/
def momentOfInertia (p : Parameters) (t : ℝ) : ℝ :=
  ∑ i, p.mass i * ‖trajectory p t i‖ ^ 2

/-- Kinetic energy from actual velocity certificates. -/
def kineticEnergy (p : Parameters) (t : ℝ) : ℝ :=
  (∑ i, p.mass i * ‖velocity p t i‖ ^ 2) / 2

/-- Gravitational potential: pairs 01, 02, and 12, each exactly once. -/
def potentialEnergy (p : Parameters) (t : ℝ) : ℝ :=
  -p.G * (p.mass 0 * p.mass 1 / ‖trajectory p t 0 - trajectory p t 1‖ +
    p.mass 0 * p.mass 2 / ‖trajectory p t 0 - trajectory p t 2‖ +
    p.mass 1 * p.mass 2 / ‖trajectory p t 1 - trajectory p t 2‖)

/-- Total mechanical energy of the rotating three-body configuration. -/
def totalEnergy (p : Parameters) (t : ℝ) : ℝ := kineticEnergy p t + potentialEnergy p t

/-- Scalar angular momentum perpendicular to the plane. -/
def totalAngularMomentum (p : Parameters) (t : ℝ) : ℝ :=
  ∑ i, p.mass i * cross (trajectory p t i) (velocity p t i)

lemma pairMassSum_pos (p : Parameters) : 0 < pairMassSum p := by
  exact add_pos
    (add_pos (mul_pos (p.mass_pos 0) (p.mass_pos 1))
      (mul_pos (p.mass_pos 0) (p.mass_pos 2)))
    (mul_pos (p.mass_pos 1) (p.mass_pos 2))

/-- Weighted Lagrange identity, valid even before imposing barycentric coordinates. -/
lemma threeBody_inertia_identity (m : Fin 3 → ℝ) (q : Fin 3 → ℂ) :
    totalMass m * (∑ i, m i * ‖q i‖ ^ 2) =
      m 0 * m 1 * ‖q 0 - q 1‖ ^ 2 +
      m 0 * m 2 * ‖q 0 - q 2‖ ^ 2 +
      m 1 * m 2 * ‖q 1 - q 2‖ ^ 2 + ‖firstMoment m q‖ ^ 2 := by
  simp [totalMass, firstMoment, Fin.sum_univ_succ, Complex.sq_norm,
    Complex.normSq_apply, Complex.real_smul, Complex.mul_re, Complex.mul_im]
  ring

lemma momentOfInertia_const (p : Parameters) (t : ℝ) :
    momentOfInertia p t = momentOfInertia p 0 := by
  unfold momentOfInertia
  apply Finset.sum_congr rfl
  intro i _
  rw [trajectory_radius, trajectory_zero]

/-- Inertia depends on the pair-mass sum, not on a mistaken geometric centroid. -/
lemma momentOfInertia_formula (p : Parameters) (t : ℝ) :
    momentOfInertia p t = p.side ^ 2 * pairMassSum p / totalMass p.mass := by
  have h := threeBody_inertia_identity p.mass (trajectory p t)
  simp only [trajectory_firstMoment, norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero,
    trajectory_equidistant p t 0 1 (by decide),
    trajectory_equidistant p t 0 2 (by decide),
    trajectory_equidistant p t 1 2 (by decide)] at h
  apply (eq_div_iff (ne_of_gt (totalMass_pos p.mass p.mass_pos))).mpr
  change (∑ i, p.mass i * ‖trajectory p t i‖ ^ 2) * totalMass p.mass =
    p.side ^ 2 * pairMassSum p
  unfold pairMassSum
  nlinarith [h]

lemma momentOfInertia_pos (p : Parameters) (t : ℝ) : 0 < momentOfInertia p t := by
  rw [momentOfInertia_formula]
  exact div_pos (mul_pos (pow_pos p.side_pos 2) (pairMassSum_pos p))
    (totalMass_pos p.mass p.mass_pos)

lemma speed_squared (p : Parameters) (t : ℝ) (i : Fin 3) :
    ‖velocity p t i‖ ^ 2 = angularSpeed p ^ 2 * ‖trajectory p t i‖ ^ 2 := by
  rw [velocity_eq_tangent, norm_tangent, abs_of_pos (angularSpeed_pos p)]
  ring

lemma kineticEnergy_inertia (p : Parameters) (t : ℝ) :
    kineticEnergy p t = angularSpeed p ^ 2 * momentOfInertia p t / 2 := by
  unfold kineticEnergy momentOfInertia
  calc
    (∑ i, p.mass i * ‖velocity p t i‖ ^ 2) / 2 =
        (∑ i, angularSpeed p ^ 2 * (p.mass i * ‖trajectory p t i‖ ^ 2)) / 2 := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [speed_squared]
      ring
    _ = angularSpeed p ^ 2 * (∑ i, p.mass i * ‖trajectory p t i‖ ^ 2) / 2 := by
      rw [Finset.mul_sum]

lemma kineticEnergy_formula (p : Parameters) (t : ℝ) :
    kineticEnergy p t = p.G * pairMassSum p / (2 * p.side) := by
  rw [kineticEnergy_inertia, angularSpeed_sq, momentOfInertia_formula]
  field_simp [ne_of_gt p.side_pos, ne_of_gt (totalMass_pos p.mass p.mass_pos)]

lemma potentialEnergy_formula (p : Parameters) (t : ℝ) :
    potentialEnergy p t = -(p.G * pairMassSum p / p.side) := by
  unfold potentialEnergy
  rw [trajectory_equidistant p t 0 1 (by decide),
    trajectory_equidistant p t 0 2 (by decide),
    trajectory_equidistant p t 1 2 (by decide)]
  unfold pairMassSum
  field_simp [ne_of_gt p.side_pos]

/-- A closed expression, independent of time, for the physical total energy. -/
lemma totalEnergy_formula (p : Parameters) (t : ℝ) :
    totalEnergy p t = -(p.G * pairMassSum p / (2 * p.side)) := by
  rw [totalEnergy, kineticEnergy_formula, potentialEnergy_formula]
  field_simp [ne_of_gt p.side_pos]
  ring

lemma totalEnergy_const (p : Parameters) (s t : ℝ) : totalEnergy p t = totalEnergy p s := by
  rw [totalEnergy_formula, totalEnergy_formula]

lemma kineticEnergy_pos (p : Parameters) (t : ℝ) : 0 < kineticEnergy p t := by
  rw [kineticEnergy_formula]
  exact div_pos (mul_pos p.G_pos (pairMassSum_pos p)) (mul_pos (by norm_num) p.side_pos)

lemma totalEnergy_neg (p : Parameters) (t : ℝ) : totalEnergy p t < 0 := by
  rw [totalEnergy_formula]
  exact neg_neg_of_pos (div_pos (mul_pos p.G_pos (pairMassSum_pos p))
    (mul_pos (by norm_num) p.side_pos))

/-- Pointwise circular-orbit virial relation, not merely a time average. -/
lemma circular_virial_relation (p : Parameters) (t : ℝ) :
    2 * kineticEnergy p t + potentialEnergy p t = 0 := by
  rw [kineticEnergy_formula, potentialEnergy_formula]
  field_simp [ne_of_gt p.side_pos]
  ring

lemma angularMomentum_inertia (p : Parameters) (t : ℝ) :
    totalAngularMomentum p t = angularSpeed p * momentOfInertia p t := by
  unfold totalAngularMomentum momentOfInertia
  simp_rw [velocity_eq_tangent, cross_tangent]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma angularMomentum_formula (p : Parameters) (t : ℝ) :
    totalAngularMomentum p t =
      angularSpeed p * (p.side ^ 2 * pairMassSum p / totalMass p.mass) := by
  rw [angularMomentum_inertia, momentOfInertia_formula]

lemma angularMomentum_const (p : Parameters) (s t : ℝ) :
    totalAngularMomentum p t = totalAngularMomentum p s := by
  rw [angularMomentum_formula, angularMomentum_formula]

lemma angularMomentum_pos (p : Parameters) (t : ℝ) : 0 < totalAngularMomentum p t := by
  rw [angularMomentum_inertia]
  exact mul_pos (angularSpeed_pos p) (momentOfInertia_pos p t)

end ClassicalMechanics.LagrangeThreeBody
