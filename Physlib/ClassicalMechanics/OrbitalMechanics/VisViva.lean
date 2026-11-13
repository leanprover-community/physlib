/-
Copyright (c) 2026 Hannah Dawe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hannah Dawe
-/

module

public import Mathlib.Analysis.Real.Sqrt

/-!
# Circular Orbit Vis Viva
The vis-viva equation relates the speed of an orbiting body to its position
and the mass of the central body.

## i. Overview

The circular-orbit case of the vis-viva equation gives the speed from the radius and the
gravitational parameter. It also relates the speed to the positive angular rate.

## ii. Key results

- `VisViva.speedCircular_sq` gives the squared speed of a circular orbit.
- `VisViva.speedCircular_eq_radius_mul_angularRate` expresses the speed using the angular rate.

## iii. Table of contents

- A. Circular orbit speed

## iv. References

* None.
-/

@[expose] public section

namespace ClassicalMechanics

/-!
## A. Circular orbit speed
-/

/-- System parameters for the vis-viva equation in circular orbital mechanics. -/
structure VisViva where
  /-- Gravitational constant. -/
  G : ℝ
  /-- Central mass body. -/
  M : ℝ
  /-- Orbiting mass body. -/
  m : ℝ

namespace VisViva

/-- Configuration space for orbital mechanics, defining the orbital radius. -/
structure ConfigurationSpace where
  /-- Orbital radius. -/
  r : ℝ

/-- The orbital speed required for a circular orbit at radius `r`. -/
noncomputable def speedCircular (sys : VisViva) (cfg : ConfigurationSpace) : ℝ :=
  Real.sqrt (sys.G * sys.M / cfg.r)

/-- Lemma: the square of the circular orbit speed equals G M / r. -/
lemma speedCircular_sq (sys : VisViva) (cfg : ConfigurationSpace) (hr : 0 < cfg.r) (hG : 0 < sys.G)
    (hM : 0 < sys.M) :
    (speedCircular sys cfg)^2 = sys.G * sys.M / cfg.r :=
  Real.sq_sqrt (by positivity)

/-- The circular speed equals the orbital radius times the positive circular angular rate. -/
lemma speedCircular_eq_radius_mul_angularRate (sys : VisViva) (cfg : ConfigurationSpace)
    (hr : 0 < cfg.r) (hG : 0 < sys.G) (hM : 0 < sys.M) :
    sys.speedCircular cfg = cfg.r * Real.sqrt (sys.G * sys.M / cfg.r ^ 3) := by
  have hmu : 0 ≤ sys.G * sys.M := (mul_pos hG hM).le
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (mul_nonneg hr.le (Real.sqrt_nonneg _))).mp
  change (sys.speedCircular cfg) ^ 2 = _
  rw [sys.speedCircular_sq cfg hr hG hM, mul_pow, Real.sq_sqrt (div_nonneg hmu (by positivity))]
  field_simp [hr.ne']

end VisViva
end ClassicalMechanics
