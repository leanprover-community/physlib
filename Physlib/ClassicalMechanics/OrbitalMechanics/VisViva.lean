/-
Copyright (c) 2026 Hannah Dawe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hannah Dawe, Jessica Syafaq Muthmaina
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Circular Orbit Vis Viva
The vis-viva equation relates the speed of an orbiting body to its position
and the mass of the central body.

## i. Overview

The circular-orbit case of the vis-viva equation gives the speed from the radius and the
gravitational parameter. It also relates the speed to the positive angular rate.

For two bodies of masses `M` and `m` on a circular orbit of separation `r`, the central body also
moves, on a circle about the barycentre. Its reflex speed, written with the orbital period from
Kepler's third law, is the radial-velocity semi-amplitude of a star with a planet on an edge-on
circular orbit.

## ii. Key results

- `VisViva.speedCircular_sq` gives the squared speed of a circular orbit.
- `VisViva.speedCircular_eq_radius_mul_angularRate` expresses the speed using the angular rate.
- `VisViva.periodTwoBody_sq` is Kepler's third law for a circular two-body orbit.
- `VisViva.reflexSpeed_pow_three` gives the cube of the reflex speed of the central body in terms of
  the period, `K³ = 2π G m³ / (P (M + m)²)`.

## iii. Table of contents

- A. System parameters and orbital radius
  - A.1. System parameters
  - A.2. Orbital radius
- B. Circular orbit speed
  - B.1. Speed from the vis-viva equation
  - B.2. Relation to the angular rate
- C. Reflex motion of the central body
  - C.1. The period of a two-body orbit
  - C.2. The reflex speed

## iv. References

* Landau & Lifshitz, Mechanics, 3rd ed., sections 13 and 15. [ref: landau_mechanics]
* Perryman, The Exoplanet Handbook, 2nd ed., chapter 2. [ref: perryman_exoplanet_handbook]
-/

@[expose] public section

namespace ClassicalMechanics

/-!
## A. System parameters and orbital radius

### A.1. System parameters
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

/-!
### A.2. Orbital radius
-/

/-- Configuration space for orbital mechanics, defining the orbital radius. -/
structure ConfigurationSpace where
  /-- Orbital radius. -/
  r : ℝ

/-!
## B. Circular orbit speed

### B.1. Speed from the vis-viva equation
-/

/-- The orbital speed required for a circular orbit at radius `r`. -/
noncomputable def speedCircular (sys : VisViva) (cfg : ConfigurationSpace) : ℝ :=
  Real.sqrt (sys.G * sys.M / cfg.r)

/-- Lemma: the square of the circular orbit speed equals G M / r. -/
lemma speedCircular_sq (sys : VisViva) (cfg : ConfigurationSpace) (hr : 0 < cfg.r) (hG : 0 < sys.G)
    (hM : 0 < sys.M) :
    (speedCircular sys cfg)^2 = sys.G * sys.M / cfg.r :=
  Real.sq_sqrt (by positivity)

/-!
### B.2. Relation to the angular rate
-/

/-- The circular speed equals the orbital radius times the positive circular angular rate. -/
lemma speedCircular_eq_radius_mul_angularRate (sys : VisViva) (cfg : ConfigurationSpace)
    (hr : 0 < cfg.r) (hG : 0 < sys.G) (hM : 0 < sys.M) :
    sys.speedCircular cfg = cfg.r * Real.sqrt (sys.G * sys.M / cfg.r ^ 3) := by
  have hmu : 0 ≤ sys.G * sys.M := (mul_pos hG hM).le
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (mul_nonneg hr.le (Real.sqrt_nonneg _))).mp
  change (sys.speedCircular cfg) ^ 2 = _
  rw [sys.speedCircular_sq cfg hr hG hM, mul_pow, Real.sq_sqrt (div_nonneg hmu (by positivity))]
  field_simp [hr.ne']

/-!
## C. Reflex motion of the central body

### C.1. The period of a two-body orbit
-/

/-- The period of a circular orbit of two bodies of masses `M` and `m` at separation `r`, from
Kepler's third law with the total mass `M + m`. -/
noncomputable def periodTwoBody (sys : VisViva) (cfg : ConfigurationSpace) : ℝ :=
  2 * Real.pi * Real.sqrt (cfg.r ^ 3 / (sys.G * (sys.M + sys.m)))

/-- Kepler's third law for a circular two-body orbit, `P² G (M + m) = 4π² r³`. -/
lemma periodTwoBody_sq (sys : VisViva) (cfg : ConfigurationSpace) (hr : 0 < cfg.r)
    (hG : 0 < sys.G) (hM : 0 < sys.M) (hm : 0 < sys.m) :
    sys.periodTwoBody cfg ^ 2 * (sys.G * (sys.M + sys.m)) = 4 * Real.pi ^ 2 * cfg.r ^ 3 := by
  have hGM : 0 < sys.G * (sys.M + sys.m) := mul_pos hG (add_pos hM hm)
  rw [periodTwoBody, mul_pow, Real.sq_sqrt (by positivity)]
  field_simp
  ring

/-!
### C.2. The reflex speed
-/

/-- The distance of the central body from the barycentre, `m r / (M + m)`. -/
noncomputable def reflexRadius (sys : VisViva) (cfg : ConfigurationSpace) : ℝ :=
  sys.m * cfg.r / (sys.M + sys.m)

/-- The reflex speed of the central body, which goes once round a circle of radius
`reflexRadius` per orbital period. For a star with a planet on an edge-on circular orbit, this is
the radial-velocity semi-amplitude `K`. -/
noncomputable def reflexSpeed (sys : VisViva) (cfg : ConfigurationSpace) : ℝ :=
  2 * Real.pi * sys.reflexRadius cfg / sys.periodTwoBody cfg

/-- The reflex speed in terms of the period, `K³ = 2π G m³ / (P (M + m)²)`. Taking the cube root
gives the radial-velocity semi-amplitude `K = (2π G / P)^{1/3} m / (M + m)^{2/3}`. -/
lemma reflexSpeed_pow_three (sys : VisViva) (cfg : ConfigurationSpace) (hr : 0 < cfg.r)
    (hG : 0 < sys.G) (hM : 0 < sys.M) (hm : 0 < sys.m) :
    sys.reflexSpeed cfg ^ 3 =
      2 * Real.pi * sys.G * sys.m ^ 3 / (sys.periodTwoBody cfg * (sys.M + sys.m) ^ 2) := by
  have hP : 0 < sys.periodTwoBody cfg := by
    have : 0 < cfg.r ^ 3 / (sys.G * (sys.M + sys.m)) := by positivity
    exact mul_pos (by positivity) (Real.sqrt_pos.mpr this)
  have hK := sys.periodTwoBody_sq cfg hr hG hM hm
  rw [reflexSpeed, reflexRadius, div_pow, div_eq_div_iff (by positivity) (by positivity)]
  field_simp
  linear_combination -hK

end VisViva
end ClassicalMechanics
