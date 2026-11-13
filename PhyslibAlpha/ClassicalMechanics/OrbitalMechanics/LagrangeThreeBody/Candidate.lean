/-
Copyright (c) 2026 Qianli Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qianli Ma
-/
module

public import PhyslibAlpha.ClassicalMechanics.OrbitalMechanics.LagrangeThreeBody.Core
public import PhyslibAlpha.ClassicalMechanics.OrbitalMechanics.LagrangeThreeBody.CircularMotion

/-!
# The explicit Lagrange triangular candidate
Parameters and formulas for arbitrary positive masses and positive side length.

## i. Overview
Use the complex plane with its Euclidean norm. First translate a concrete
triangle to its mass centre, then rotate at the mass-dependent angular speed.
The geometric, differential, and periodicity claims are developed in later modules.

## ii. Key results
* `angularSpeed_sq`: the required angular-speed equation
* `initialConfig_firstMoment`: the actual mass-centred seed
* `trajectory`: the explicit all-real-time candidate

## iii. Table of contents
- A. Physical parameters
- B. Explicit seed and trajectory

## iv. References

Chenciner and Féjoz, [ref: chenciner_fejoz_2008], §8, gives the equilateral
reduction of the Newtonian equations for arbitrary masses.
The Lean construction is adapted from [ref: ma_lagrange_three_body_lean].
-/

@[expose] public noncomputable section
namespace ClassicalMechanics.LagrangeThreeBody

/-!
## A. Physical parameters
-/

/-- Only physical input data; no equation of motion is assumed as a field. -/
structure Parameters where
  /-- Positive gravitational constant in consistent units. -/
  G : ℝ
  /-- Three arbitrary positive masses. -/
  mass : Fin 3 → ℝ
  /-- Positive common side length. -/
  side : ℝ
  /-- Positivity of the gravitational constant. -/
  G_pos : 0 < G
  /-- Positivity of every mass. -/
  mass_pos : ∀ i, 0 < mass i
  /-- Excludes the degenerate, colliding triangle. -/
  side_pos : 0 < side

/-- Counterclockwise angular speed; clockwise motion can be obtained separately. -/
def angularSpeed (p : Parameters) : ℝ :=
  Real.sqrt (p.G * totalMass p.mass / p.side ^ 3)

/-- The coefficient under the square root is strictly positive. -/
lemma frequencyCoefficient_pos (p : Parameters) :
    0 < p.G * totalMass p.mass / p.side ^ 3 := by
  exact div_pos (mul_pos p.G_pos (totalMass_pos p.mass p.mass_pos))
    (pow_pos p.side_pos 3)

/-- The chosen angular speed is strictly positive. -/
lemma angularSpeed_pos (p : Parameters) : 0 < angularSpeed p := by
  exact Real.sqrt_pos.2 (frequencyCoefficient_pos p)

/-- The speed is derived from the parameters, not postulated as a law. -/
lemma angularSpeed_sq (p : Parameters) :
    angularSpeed p ^ 2 = p.G * totalMass p.mass / p.side ^ 3 := by
  exact Real.sq_sqrt (le_of_lt (frequencyCoefficient_pos p))

/-!
## B. Explicit seed and trajectory
-/

/-- Concrete side-`ℓ` triangle; equidistance is developed in `Geometry.lean`. -/
def rawTriangle (ℓ : ℝ) : Fin 3 → ℂ :=
  ![0, (ℓ : ℂ), (⟨ℓ / 2, Real.sqrt 3 * ℓ / 2⟩ : ℂ)]

/-- Translate by the weighted mass centre, which depends on the three masses. -/
def initialConfig (p : Parameters) : Fin 3 → ℂ :=
  centeredPositions p.mass (rawTriangle p.side)

/-- The specified initial configuration has zero first mass moment. -/
lemma initialConfig_firstMoment (p : Parameters) :
    firstMoment p.mass (initialConfig p) = 0 := by
  exact firstMoment_centered p.mass (rawTriangle p.side)
    (ne_of_gt (totalMass_pos p.mass p.mass_pos))

/-- The explicit orbit, defined for every real time, in a Euclidean plane. -/
def trajectory (p : Parameters) (t : ℝ) (i : Fin 3) : ℂ :=
  ⟨xCoordinate (angularSpeed p) (initialConfig p i).re (initialConfig p i).im t,
   yCoordinate (angularSpeed p) (initialConfig p i).re (initialConfig p i).im t⟩

/-- Explicit candidate velocity; its vector derivative certificate is in `Dynamics.lean`. -/
def velocity (p : Parameters) (t : ℝ) (i : Fin 3) : ℂ :=
  ⟨xVelocity (angularSpeed p) (initialConfig p i).re (initialConfig p i).im t,
   yVelocity (angularSpeed p) (initialConfig p i).re (initialConfig p i).im t⟩

/-- Explicit period; its positivity and periodicity proofs are in `Periodicity.lean`. -/
def orbitPeriod (p : Parameters) : ℝ := 2 * Real.pi / angularSpeed p

/-- The target acceptance predicate requires actual derivatives, not a declared acceleration.
The explicit witness is supplied in `Dynamics.lean`; the predicate itself assumes no solution. -/
def SatisfiesNewton (p : Parameters) (r v : ℝ → Fin 3 → ℂ) : Prop :=
  (∀ t i, HasDerivAt (fun s => r s i) (v t i) t) ∧
  (∀ t i, HasDerivAt (fun s => v s i)
    (gravityAcceleration p.G p.mass (r t) i) t) ∧
  (∀ t, Function.Injective (r t))

end ClassicalMechanics.LagrangeThreeBody
