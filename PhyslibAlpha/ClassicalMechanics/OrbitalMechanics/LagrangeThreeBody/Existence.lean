/-
Copyright (c) 2026 Qianli Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qianli Ma
-/
module

public import PhyslibAlpha.ClassicalMechanics.OrbitalMechanics.LagrangeThreeBody.Periodicity

/-!
# Existence of a circular equilateral orbit
The explicit orbit gives a certificate of existence for positive masses and side length.

## i. Overview

The certificate collects the equations of motion, equilateral geometry, mass centring,
periodicity, and the specified initial position and velocity.

## ii. Key results

- `exists_lagrange_for_positive_data` gives the main result of this module.

## iii. Table of contents

- A. The orbit certificate

## iv. References

Chenciner and Féjoz, [ref: chenciner_fejoz_2008], §8, gives the equilateral
reduction of the Newtonian equations for arbitrary masses.
The Lean construction is adapted from [ref: ma_lagrange_three_body_lean].
-/

@[expose] public noncomputable section
namespace ClassicalMechanics.LagrangeThreeBody

/-!
## A. The orbit certificate
-/

/-- The equations of motion, geometry, periodicity, and initial data of the orbit. -/
structure CircularOrbitCertificate (p : Parameters)
    (r v : ℝ → Fin 3 → ℂ) (T : ℝ) : Prop where
  equations : SatisfiesNewton p r v
  equilateral : ∀ t, Equidistant (r t) p.side
  barycentric : ∀ t, firstMoment p.mass (r t) = 0
  positivePeriod : 0 < T
  positionPeriodic : ∀ i, Function.Periodic (fun t => r t i) T
  velocityPeriodic : ∀ i, Function.Periodic (fun t => v t i) T
  initialPosition : ∀ i, r 0 i = initialConfig p i
  initialVelocity : ∀ i, v 0 i = tangent (angularSpeed p) (initialConfig p i)
  periodLaw : T ^ 2 * (p.G * totalMass p.mass) = 4 * Real.pi ^ 2 * p.side ^ 3

/-- Main explicit theorem: arbitrary positive masses and positive side length. -/
lemma lagrange_circular_solution (p : Parameters) :
    CircularOrbitCertificate p (trajectory p) (velocity p) (orbitPeriod p) where
  equations := trajectory_satisfiesNewton p
  equilateral := trajectory_equidistant p
  barycentric := trajectory_firstMoment p
  positivePeriod := orbitPeriod_pos p
  positionPeriodic := trajectory_periodic p
  velocityPeriodic := velocity_periodic p
  initialPosition := trajectory_zero p
  initialVelocity := velocity_zero p
  periodLaw := kepler_period_law p

/-- An existence statement with explicit witnesses, not a conditional force identity. -/
lemma exists_lagrange_circular_solution (p : Parameters) :
    ∃ (r v : ℝ → Fin 3 → ℂ) (T : ℝ), CircularOrbitCertificate p r v T := by
  exact ⟨trajectory p, velocity p, orbitPeriod p, lagrange_circular_solution p⟩

/-- Standalone version exposing only physical input data and ordinary conclusions. -/
lemma exists_lagrange_for_positive_data (G : ℝ) (m : Fin 3 → ℝ) (ℓ : ℝ)
    (hG : 0 < G) (hm : ∀ i, 0 < m i) (hℓ : 0 < ℓ) :
    ∃ (r v : ℝ → Fin 3 → ℂ) (T : ℝ),
      0 < T ∧
      (∀ t i, HasDerivAt (fun s => r s i) (v t i) t) ∧
      (∀ t i, HasDerivAt (fun s => v s i) (gravityAcceleration G m (r t) i) t) ∧
      (∀ t, Function.Injective (r t)) ∧
      (∀ t, Equidistant (r t) ℓ) ∧
      (∀ t, firstMoment m (r t) = 0) ∧
      (∀ i, Function.Periodic (fun t => r t i) T) ∧
      (∀ i, Function.Periodic (fun t => v t i) T) ∧
      T ^ 2 * (G * totalMass m) = 4 * Real.pi ^ 2 * ℓ ^ 3 := by
  let p : Parameters := ⟨G, m, ℓ, hG, hm, hℓ⟩
  refine ⟨trajectory p, velocity p, orbitPeriod p, orbitPeriod_pos p, ?_⟩
  exact ⟨hasDerivAt_trajectory p, hasDerivAt_velocity p, trajectory_noCollision p,
    trajectory_equidistant p, trajectory_firstMoment p, trajectory_periodic p,
    velocity_periodic p, kepler_period_law p⟩

end ClassicalMechanics.LagrangeThreeBody
