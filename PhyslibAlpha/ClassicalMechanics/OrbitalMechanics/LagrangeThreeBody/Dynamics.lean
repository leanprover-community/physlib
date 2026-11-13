/-
Copyright (c) 2026 Qianli Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qianli Ma
-/
module

public import PhyslibAlpha.ClassicalMechanics.OrbitalMechanics.LagrangeThreeBody.Geometry

/-!
# Newtonian dynamics of the Lagrange orbit
The rotating trajectories satisfy the Newtonian three-body equations.

## i. Overview

Equal distances and zero first mass moment make the acceleration proportional to position.
Differentiating the rotating trajectories gives the same acceleration.

## ii. Key results

- `trajectory_satisfiesNewton` gives the main result of this module.

## iii. Table of contents

- A. Newtonian equations of motion

## iv. References

Chenciner and Féjoz, [ref: chenciner_fejoz_2008], §8, gives the equilateral
reduction of the Newtonian equations for arbitrary masses.
The Lean construction is adapted from [ref: ma_lagrange_three_body_lean].
-/

@[expose] public noncomputable section
open scoped BigOperators
namespace ClassicalMechanics.LagrangeThreeBody

/-!
## A. Newtonian equations of motion
-/

lemma trajectory_gravity (p : Parameters) (t : ℝ) (i : Fin 3) :
    gravityAcceleration p.G p.mass (trajectory p t) i =
      -(p.G * totalMass p.mass / p.side ^ 3) • trajectory p t i := by
  exact gravityAcceleration_eq_of_centered p.G p.side p.mass (trajectory p t)
    (trajectory_equidistant p t) (trajectory_firstMoment p t) i

lemma hasDerivAt_trajectory (p : Parameters) (t : ℝ) (i : Fin 3) :
    HasDerivAt (fun s => trajectory p s i) (velocity p t i) t := by
  simpa only [trajectory_eq_rotate, velocity_eq_rotateVelocity] using
    hasDerivAt_rotating (angularSpeed p) (initialConfig p i) t

lemma hasDerivAt_velocity_harmonic (p : Parameters) (t : ℝ) (i : Fin 3) :
    HasDerivAt (fun s => velocity p s i)
      (-(angularSpeed p ^ 2) • trajectory p t i) t := by
  simpa only [trajectory_eq_rotate, velocity_eq_rotateVelocity] using
    hasDerivAt_rotatingVelocity (angularSpeed p) (initialConfig p i) t

/-- Actual acceleration equals the sum of the other two bodies' attractions. -/
lemma hasDerivAt_velocity (p : Parameters) (t : ℝ) (i : Fin 3) :
    HasDerivAt (fun s => velocity p s i)
      (gravityAcceleration p.G p.mass (trajectory p t) i) t := by
  rw [trajectory_gravity, ← angularSpeed_sq]
  exact hasDerivAt_velocity_harmonic p t i

/-- The explicit, collision-free solution of the Newtonian system. -/
lemma trajectory_satisfiesNewton (p : Parameters) :
    SatisfiesNewton p (trajectory p) (velocity p) := by
  exact ⟨hasDerivAt_trajectory p, hasDerivAt_velocity p, trajectory_noCollision p⟩

lemma deriv_trajectory (p : Parameters) (i : Fin 3) :
    deriv (fun t => trajectory p t i) = fun t => velocity p t i := by
  funext t
  exact (hasDerivAt_trajectory p t i).deriv

/-- The usual second-order Newton equation, with `deriv` appearing literally. -/
lemma second_deriv_trajectory (p : Parameters) (t : ℝ) (i : Fin 3) :
    deriv (deriv (fun s => trajectory p s i)) t =
      gravityAcceleration p.G p.mass (trajectory p t) i := by
  rw [deriv_trajectory]
  exact (hasDerivAt_velocity p t i).deriv

lemma trajectory_differentiable (p : Parameters) (i : Fin 3) :
    Differentiable ℝ (fun t => trajectory p t i) := by
  intro t
  exact (hasDerivAt_trajectory p t i).differentiableAt

lemma velocity_differentiable (p : Parameters) (i : Fin 3) :
    Differentiable ℝ (fun t => velocity p t i) := by
  intro t
  exact (hasDerivAt_velocity p t i).differentiableAt

lemma trajectory_continuous (p : Parameters) (i : Fin 3) :
    Continuous (fun t => trajectory p t i) :=
  (trajectory_differentiable p i).continuous

lemma velocity_continuous (p : Parameters) (i : Fin 3) :
    Continuous (fun t => velocity p t i) :=
  (velocity_differentiable p i).continuous

/-- The physical force includes the mass of the accelerated body. -/
def gravitationalForce (p : Parameters) (q : Fin 3 → ℂ) (i : Fin 3) : ℂ :=
  ∑ j, if j = i then 0 else
    (p.G * p.mass i * p.mass j / ‖q j - q i‖ ^ 3) • (q j - q i)

lemma mass_smul_gravity (p : Parameters) (q : Fin 3 → ℂ) (i : Fin 3) :
    p.mass i • gravityAcceleration p.G p.mass q i = gravitationalForce p q i := by
  unfold gravityAcceleration gravitationalForce
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hji : j = i
  · simp [hji]
  · simp only [ite_eq_right hji, smul_smul]
    congr 1
    ring

/-- Newton's second law in literal `mass × second derivative = force` form. -/
lemma newton_second_law_force (p : Parameters) (t : ℝ) (i : Fin 3) :
    p.mass i • deriv (deriv (fun s => trajectory p s i)) t =
      gravitationalForce p (trajectory p t) i := by
  rw [second_deriv_trajectory, mass_smul_gravity]

/-- The barycentric orbit has zero total linear momentum at every real time. -/
lemma velocity_firstMoment (p : Parameters) (t : ℝ) :
    firstMoment p.mass (velocity p t) = 0 := by
  have hv : velocity p t = fun i => tangent (angularSpeed p) (trajectory p t i) := by
    funext i
    exact velocity_eq_tangent p t i
  rw [hv, firstMoment_tangent, trajectory_firstMoment]
  simp [tangent]

end ClassicalMechanics.LagrangeThreeBody
