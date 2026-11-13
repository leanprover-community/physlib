/-
Copyright (c) 2026 Qianli Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qianli Ma
-/
module

public import PhyslibAlpha.ClassicalMechanics.OrbitalMechanics.LagrangeThreeBody.Frames

/-!
# The Lagrange orbit from an arbitrary equilateral seed
Any labelled equilateral seed gives a circular solution with explicit initial velocities.

## i. Overview

The positions are centred at their mass barycentre and rotated at the angular speed
determined by the total mass and side length. The initial barycentre is then restored.

## ii. Key results

- `arbitrary_equilateral_seed_certificate` gives the main result of this module.

## iii. Table of contents

- A. Construction from a labelled seed

## iv. References

Chenciner and Féjoz, [ref: chenciner_fejoz_2008], §8, gives the equilateral
reduction of the Newtonian equations for arbitrary masses.
The Lean construction is adapted from [ref: ma_lagrange_three_body_lean].
-/

@[expose] public noncomputable section
namespace ClassicalMechanics.LagrangeThreeBody

/-!
## A. Construction from a labelled seed
-/

/-- Position obtained by rotating a seed about the origin. -/
def seedPosition (p : Parameters) (q : Fin 3 → ℂ) (t : ℝ) (i : Fin 3) : ℂ :=
  rotate (angularSpeed p * t) (q i)

/-- Tangent velocity of a seed rotating about the origin. -/
def seedVelocity (p : Parameters) (q : Fin 3 → ℂ) (t : ℝ) (i : Fin 3) : ℂ :=
  rotateVelocity (angularSpeed p) (angularSpeed p * t) (q i)

lemma seedPosition_equidistant (p : Parameters) (q : Fin 3 → ℂ)
    (hq : Equidistant q p.side) (t : ℝ) :
    Equidistant (seedPosition p q t) p.side := by
  intro i j hij
  change ‖rotate (angularSpeed p * t) (q i) -
    rotate (angularSpeed p * t) (q j)‖ = p.side
  rw [rotate_pair_distance]
  exact hq i j hij

lemma seedPosition_firstMoment (p : Parameters) (q : Fin 3 → ℂ)
    (hc : firstMoment p.mass q = 0) (t : ℝ) :
    firstMoment p.mass (seedPosition p q t) = 0 := by
  change firstMoment p.mass (fun i => rotate (angularSpeed p * t) (q i)) = 0
  rw [firstMoment_rotate, hc, rotate_zero_vector]

/-- The central-configuration argument works for every equilateral centred seed. -/
lemma seedPosition_satisfiesNewton (p : Parameters) (q : Fin 3 → ℂ)
    (hq : Equidistant q p.side) (hc : firstMoment p.mass q = 0) :
    SatisfiesNewton p (seedPosition p q) (seedVelocity p q) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t i
    exact hasDerivAt_rotating (angularSpeed p) (q i) t
  · intro t i
    have hg := gravityAcceleration_eq_of_centered p.G p.side p.mass
      (seedPosition p q t) (seedPosition_equidistant p q hq t)
      (seedPosition_firstMoment p q hc t) i
    rw [hg, ← angularSpeed_sq]
    exact hasDerivAt_rotatingVelocity (angularSpeed p) (q i) t
  · intro t
    exact equidistant_injective (seedPosition p q t) p.side
      (seedPosition_equidistant p q hq t) p.side_pos

lemma centeredSeed_equidistant (p : Parameters) (q : Fin 3 → ℂ)
    (hq : Equidistant q p.side) :
    Equidistant (centeredPositions p.mass q) p.side := by
  intro i j hij
  rw [centeredPositions_sub]
  exact hq i j hij

/-- The orbit with the original seed's mass centre fixed at its original place. -/
def seededOrbit (p : Parameters) (q : Fin 3 → ℂ) : ℝ → Fin 3 → ℂ :=
  framePosition (seedPosition p (centeredPositions p.mass q))
    (centerOfMass p.mass q) 0

/-- Velocities of the orbit from the supplied equilateral initial positions. -/
def seededVelocity (p : Parameters) (q : Fin 3 → ℂ) : ℝ → Fin 3 → ℂ :=
  frameVelocity (seedVelocity p (centeredPositions p.mass q)) 0

/-- This solves the equations for any given equilateral initial positions. -/
lemma arbitrary_equilateral_seed_solution (p : Parameters) (q : Fin 3 → ℂ)
    (hq : Equidistant q p.side) :
    SatisfiesNewton p (seededOrbit p q) (seededVelocity p q) := by
  apply satisfiesNewton_frame
  exact seedPosition_satisfiesNewton p (centeredPositions p.mass q)
    (centeredSeed_equidistant p q hq)
    (firstMoment_centered p.mass q (ne_of_gt (totalMass_pos p.mass p.mass_pos)))

/-- The constructed orbit really starts at the supplied positions, not at a
silently substituted canonical triangle. -/
lemma seededOrbit_initial (p : Parameters) (q : Fin 3 → ℂ) (i : Fin 3) :
    seededOrbit p q 0 i = q i := by
  simp [seededOrbit, framePosition, seedPosition, centeredPositions]

lemma seededVelocity_initial (p : Parameters) (q : Fin 3 → ℂ) (i : Fin 3) :
    seededVelocity p q 0 i =
      tangent (angularSpeed p) (q i - centerOfMass p.mass q) := by
  simp [seededVelocity, frameVelocity, seedVelocity, rotateVelocity,
    centeredPositions]

lemma seededOrbit_equidistant (p : Parameters) (q : Fin 3 → ℂ)
    (hq : Equidistant q p.side) (t : ℝ) :
    Equidistant (seededOrbit p q t) p.side := by
  intro i j hij
  simpa only [seededOrbit, framePosition, translated_pair_sub] using
    seedPosition_equidistant p (centeredPositions p.mass q)
      (centeredSeed_equidistant p q hq) t i j hij

lemma seededOrbit_periodic (p : Parameters) (q : Fin 3 → ℂ) (i : Fin 3) :
    Function.Periodic (fun t => seededOrbit p q t i) (orbitPeriod p) := by
  intro t
  simp only [seededOrbit, framePosition, mul_zero, add_zero, seedPosition]
  exact congrArg (fun z : ℂ => z + centerOfMass p.mass q)
    (rotate_periodic (angularSpeed p) (ne_of_gt (angularSpeed_pos p))
      (centeredPositions p.mass q i) t)

lemma seededVelocity_periodic (p : Parameters) (q : Fin 3 → ℂ) (i : Fin 3) :
    Function.Periodic (fun t => seededVelocity p q t i) (orbitPeriod p) := by
  simpa only [seededVelocity, frameVelocity, add_zero, seedVelocity, orbitPeriod]
    using rotateVelocity_periodic (angularSpeed p)
      (ne_of_gt (angularSpeed_pos p)) (centeredPositions p.mass q i)

/-- A reusable all-in-one conclusion for a freely positioned/oriented seed. -/
lemma arbitrary_equilateral_seed_certificate (p : Parameters) (q : Fin 3 → ℂ)
    (hq : Equidistant q p.side) :
    SatisfiesNewton p (seededOrbit p q) (seededVelocity p q) ∧
    (∀ i, seededOrbit p q 0 i = q i) ∧
    (∀ t, Equidistant (seededOrbit p q t) p.side) ∧
    (∀ i, Function.Periodic (fun t => seededOrbit p q t i) (orbitPeriod p)) ∧
    (∀ i, Function.Periodic (fun t => seededVelocity p q t i) (orbitPeriod p)) := by
  exact ⟨arbitrary_equilateral_seed_solution p q hq, seededOrbit_initial p q,
    seededOrbit_equidistant p q hq, seededOrbit_periodic p q,
    seededVelocity_periodic p q⟩

end ClassicalMechanics.LagrangeThreeBody
