/-
Copyright (c) 2026 Chengyuan AI Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chengyuan AI Lab
-/
module

public import PhyslibAlpha.ClassicalMechanics.OrbitalMechanics.Hohmann.Optimality.PhysicalUnits

/-!
# Planar states for the Hohmann comparison

Cartesian velocity jumps can be evaluated in polar components.

## i. Overview

The endpoint velocity is compared with the prograde circular velocity at the same position. The
squared Euclidean norm decomposes into a radial square and a tangential difference squared.

## ii. Key results

- `PlanarState.impulse_polar` gives the main result of this module.

## iii. Table of contents

- A. Cartesian and polar endpoint data

## iv. References

- [ref: hohmann_prussing_1992]. Prussing studies the two-impulse global comparison.
-/

@[expose] public noncomputable section

namespace ClassicalMechanics.HohmannOptimality

/-!
## A. Cartesian and polar endpoint data
-/

/-- The Cartesian position and velocity of a particle in the orbital plane. -/
structure PlanarState where
  /-- The first Cartesian position coordinate. -/
  x : ℝ
  /-- The second Cartesian position coordinate. -/
  y : ℝ
  /-- The first Cartesian velocity coordinate. -/
  vx : ℝ
  /-- The second Cartesian velocity coordinate. -/
  vy : ℝ

namespace PlanarState

/-- The Euclidean distance from the attracting centre. -/
def radius (z : PlanarState) : ℝ := Real.sqrt (z.x^2+z.y^2)
/-- The signed angular momentum per unit mass. -/
def angular (z : PlanarState) : ℝ := z.x*z.vy-z.y*z.vx
/-- The component of the velocity along the outward radial direction. -/
def radial (z : PlanarState) : ℝ := (z.x*z.vx+z.y*z.vy)/z.radius
/-- The velocity component in the prograde tangential direction. -/
def tangent (z : PlanarState) : ℝ := z.angular/z.radius
/-- Twice the sum of kinetic and gravitational potential energy per unit mass. -/
def energy (z : PlanarState) (mu : ℝ) : ℝ := z.vx^2+z.vy^2-2*mu/z.radius
/-- Actual Cartesian speed change to/from the same prograde circular velocity. -/
def impulse (z : PlanarState) (c : ℝ) : ℝ :=
  Real.sqrt ((z.vx+c*z.y/z.radius)^2+(z.vy-c*z.x/z.radius)^2)

lemma radius_sq (z : PlanarState) : z.radius^2=z.x^2+z.y^2 :=
  Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))
lemma radius_mul_tangent (z : PlanarState) (hr : 0 < z.radius) :
    z.radius*z.tangent = z.angular := by
  dsimp [tangent]
  field_simp [ne_of_gt hr]
lemma polar_speed_sq (z : PlanarState) (hr : 0 < z.radius) :
    z.radial^2+z.tangent^2=z.vx^2+z.vy^2 := by
  have hi : (z.x*z.vx+z.y*z.vy)^2+(z.x*z.vy-z.y*z.vx)^2 =
      (z.x^2+z.y^2)*(z.vx^2+z.vy^2) := by ring
  dsimp [radial, tangent, angular]
  field_simp [ne_of_gt hr]
  nlinarith [congrArg (fun u : ℝ => u*(z.vx^2+z.vy^2)) z.radius_sq]
lemma impulse_polar (z : PlanarState) (c : ℝ) (hr : 0 < z.radius) :
    z.impulse c = Real.sqrt (z.radial^2+(z.tangent-c)^2) := by
  unfold impulse
  congr 1
  dsimp [radial, tangent, angular]
  field_simp [ne_of_gt hr]
  nlinarith [congrArg (fun u : ℝ => u*(z.vx^2+z.vy^2-c^2)) z.radius_sq]

end PlanarState
end ClassicalMechanics.HohmannOptimality
