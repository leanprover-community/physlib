/-
Copyright (c) 2026 Qianli Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qianli Ma
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Explicit circular kinematics
Coordinate-wise derivative certificates for a uniformly rotating plane vector.

## i. Overview
Prove actual `HasDerivAt` statements, rather than assigning an acceleration by
its intended formula. The two scalar coordinates will later be combined in the
Euclidean complex plane. No product-type supremum norm is used as a distance.

## ii. Key results
* `hasDerivAt_xCoordinate`, `hasDerivAt_yCoordinate`: velocity
* `hasDerivAt_xVelocity`, `hasDerivAt_yVelocity`: acceleration
* `second_deriv_xCoordinate`, `second_deriv_yCoordinate`: harmonic equations
* `rotation_squared_length`: preservation of Euclidean squared length

## iii. Table of contents
- A. Explicit coordinate formulas
- B. Derivative certificates
- C. Second derivatives and length preservation

## iv. References

Chenciner and Féjoz, [ref: chenciner_fejoz_2008], §8, gives the equilateral
reduction of the Newtonian equations for arbitrary masses.
The Lean construction is adapted from [ref: ma_lagrange_three_body_lean].
-/

@[expose] public noncomputable section
namespace ClassicalMechanics.LagrangeThreeBody

/-!
## A. Explicit coordinate formulas
-/

/-- Horizontal coordinate of the vector `(x,y)` rotated through `ω*t`. -/
def xCoordinate (ω x y t : ℝ) : ℝ :=
  Real.cos (ω * t) * x - Real.sin (ω * t) * y

/-- Vertical coordinate of the vector `(x,y)` rotated through `ω*t`. -/
def yCoordinate (ω x y t : ℝ) : ℝ :=
  Real.sin (ω * t) * x + Real.cos (ω * t) * y

/-- Proposed horizontal velocity, certified below by differentiation. -/
def xVelocity (ω x y t : ℝ) : ℝ :=
  -ω * Real.sin (ω * t) * x - ω * Real.cos (ω * t) * y

/-- Proposed vertical velocity, certified below by differentiation. -/
def yVelocity (ω x y t : ℝ) : ℝ :=
  ω * Real.cos (ω * t) * x - ω * Real.sin (ω * t) * y

/-!
## B. Derivative certificates
-/

/-- First derivative of the horizontal coordinate. -/
lemma hasDerivAt_xCoordinate (ω x y t : ℝ) :
    HasDerivAt (xCoordinate ω x y) (xVelocity ω x y t) t := by
  have hp : HasDerivAt (fun s : ℝ => ω * s) ω t := by
    simpa using (hasDerivAt_id t).const_mul ω
  convert (hp.cos.mul_const x).sub (hp.sin.mul_const y) using 1
  · rfl
  · dsimp only [xCoordinate, xVelocity]
    ring

/-- First derivative of the vertical coordinate. -/
lemma hasDerivAt_yCoordinate (ω x y t : ℝ) :
    HasDerivAt (yCoordinate ω x y) (yVelocity ω x y t) t := by
  have hp : HasDerivAt (fun s : ℝ => ω * s) ω t := by
    simpa using (hasDerivAt_id t).const_mul ω
  convert (hp.sin.mul_const x).add (hp.cos.mul_const y) using 1
  · rfl
  · dsimp only [yCoordinate, yVelocity]
    ring

/-- Horizontal acceleration is minus angular-speed squared times position. -/
lemma hasDerivAt_xVelocity (ω x y t : ℝ) :
    HasDerivAt (xVelocity ω x y) (-(ω ^ 2) * xCoordinate ω x y t) t := by
  have hp : HasDerivAt (fun s : ℝ => ω * s) ω t := by
    simpa using (hasDerivAt_id t).const_mul ω
  convert ((hp.sin.const_mul (-ω)).mul_const x).sub
    ((hp.cos.const_mul ω).mul_const y) using 1
  · rfl
  · dsimp only [xVelocity, xCoordinate]
    ring

/-- Vertical acceleration is minus angular-speed squared times position. -/
lemma hasDerivAt_yVelocity (ω x y t : ℝ) :
    HasDerivAt (yVelocity ω x y) (-(ω ^ 2) * yCoordinate ω x y t) t := by
  have hp : HasDerivAt (fun s : ℝ => ω * s) ω t := by
    simpa using (hasDerivAt_id t).const_mul ω
  convert ((hp.cos.const_mul ω).mul_const x).sub
    ((hp.sin.const_mul ω).mul_const y) using 1
  · rfl
  · dsimp only [yVelocity, yCoordinate]
    ring

/-!
## C. Second derivatives and length preservation
-/

/-- Actual iterated scalar derivative in the horizontal coordinate. -/
lemma second_deriv_xCoordinate (ω x y t : ℝ) :
    deriv (deriv (xCoordinate ω x y)) t = -(ω ^ 2) * xCoordinate ω x y t := by
  have hv : deriv (xCoordinate ω x y) = xVelocity ω x y := by
    funext s
    exact (hasDerivAt_xCoordinate ω x y s).deriv
  rw [hv]
  exact (hasDerivAt_xVelocity ω x y t).deriv

/-- Actual iterated scalar derivative in the vertical coordinate. -/
lemma second_deriv_yCoordinate (ω x y t : ℝ) :
    deriv (deriv (yCoordinate ω x y)) t = -(ω ^ 2) * yCoordinate ω x y t := by
  have hv : deriv (yCoordinate ω x y) = yVelocity ω x y := by
    funext s
    exact (hasDerivAt_yCoordinate ω x y s).deriv
  rw [hv]
  exact (hasDerivAt_yVelocity ω x y t).deriv

/-- Rotation preserves Euclidean squared length, with no approximation. -/
lemma rotation_squared_length (ω x y t : ℝ) :
    (xCoordinate ω x y t) ^ 2 + (yCoordinate ω x y t) ^ 2 = x ^ 2 + y ^ 2 := by
  calc
    (xCoordinate ω x y t) ^ 2 + (yCoordinate ω x y t) ^ 2 =
        (x ^ 2 + y ^ 2) * (Real.sin (ω * t) ^ 2 + Real.cos (ω * t) ^ 2) := by
      unfold xCoordinate yCoordinate
      ring
    _ = x ^ 2 + y ^ 2 := by rw [Real.sin_sq_add_cos_sq, mul_one]

end ClassicalMechanics.LagrangeThreeBody
