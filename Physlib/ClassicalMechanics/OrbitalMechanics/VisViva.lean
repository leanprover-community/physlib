/-
Copyright (c) 2026 Hannah Dawe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hannah Dawe, Jessica Syafaq Muthmaina
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Vis viva for circular orbits and the escape speed
The vis-viva equation relates the speed of an orbiting body to its position
and the mass of the central body.

## i. Overview

The circular-orbit case of the vis-viva equation gives the speed from the radius and the
gravitational parameter. It also relates the speed to the positive angular rate.

Two mass conventions appear. The circular speed, the specific orbital energy and the escape speed
use the gravitational parameter `G M` of the central body alone, the limit of a test body with
`m ≪ M`. The period of the two-body orbit and the reflex motion use the total mass `M + m`.

For two bodies of masses `M` and `m` on a circular orbit of separation `r`, the central body also
moves, on a circle about the barycentre. Its reflex speed, written with the orbital period from
Kepler's third law, is the radial-velocity semi-amplitude of a star with a planet on an edge-on
circular orbit.

The specific orbital energy `v² / 2 - G M / r` is negative on a circular orbit, where it equals
half the potential energy per unit mass, and vanishes at the escape speed `√(2 G M / r)`, which
is `√2` times the circular speed at the same radius.

## ii. Key results

- `VisViva.speedCircular_sq` gives the squared speed of a circular orbit.
- `VisViva.speedCircular_eq_radius_mul_angularRate` expresses the speed using the angular rate.
- `VisViva.periodTwoBody_sq` is Kepler's third law for a circular two-body orbit.
- `VisViva.reflexSpeed_pow_three` gives the cube of the reflex speed of the central body in terms of
  the period, `K³ = 2π G m³ / (P (M + m)²)`.
- `VisViva.specificOrbitalEnergy_speedCircular` and `VisViva.specificOrbitalEnergy_speedEscape`
  evaluate the specific orbital energy on a circular orbit and at the escape speed.
- `VisViva.speedEscape_eq_sqrt_two_mul_speedCircular` and `VisViva.speedCircular_lt_speedEscape`
  relate the escape speed to the circular speed.

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
- D. Escape speed
  - D.1. The specific orbital energy
  - D.2. The escape speed
  - D.3. Relation to the circular speed

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

/-!
## D. Escape speed

### D.1. The specific orbital energy
-/

/-- The specific orbital energy of the orbiting body moving at speed `v` at radius `r`: the
kinetic energy per unit mass `v² / 2` plus the gravitational potential energy per unit mass
`-G M / r`. -/
noncomputable def specificOrbitalEnergy (sys : VisViva) (cfg : ConfigurationSpace) (v : ℝ) : ℝ :=
  v ^ 2 / 2 - sys.G * sys.M / cfg.r

/-- On a circular orbit the specific orbital energy is `-(G M / r) / 2`, half the potential
energy per unit mass. -/
lemma specificOrbitalEnergy_speedCircular (sys : VisViva) (cfg : ConfigurationSpace)
    (hr : 0 < cfg.r) (hG : 0 < sys.G) (hM : 0 < sys.M) :
    sys.specificOrbitalEnergy cfg (sys.speedCircular cfg) = -(sys.G * sys.M / cfg.r) / 2 := by
  rw [specificOrbitalEnergy, sys.speedCircular_sq cfg hr hG hM]
  ring

/-!
### D.2. The escape speed
-/

/-- The escape speed from radius `r`, `√(2 G M / r)`: the speed at which the specific orbital
energy vanishes, so that the body can just reach infinite separation. -/
noncomputable def speedEscape (sys : VisViva) (cfg : ConfigurationSpace) : ℝ :=
  Real.sqrt (2 * sys.G * sys.M / cfg.r)

/-- The square of the escape speed equals `2 G M / r`. -/
lemma speedEscape_sq (sys : VisViva) (cfg : ConfigurationSpace) (hr : 0 < cfg.r)
    (hG : 0 < sys.G) (hM : 0 < sys.M) :
    sys.speedEscape cfg ^ 2 = 2 * sys.G * sys.M / cfg.r :=
  Real.sq_sqrt (by positivity)

/-- The escape speed is positive. -/
lemma speedEscape_pos (sys : VisViva) (cfg : ConfigurationSpace) (hr : 0 < cfg.r)
    (hG : 0 < sys.G) (hM : 0 < sys.M) :
    0 < sys.speedEscape cfg :=
  Real.sqrt_pos.mpr (by positivity)

/-- At the escape speed the specific orbital energy vanishes. -/
lemma specificOrbitalEnergy_speedEscape (sys : VisViva) (cfg : ConfigurationSpace)
    (hr : 0 < cfg.r) (hG : 0 < sys.G) (hM : 0 < sys.M) :
    sys.specificOrbitalEnergy cfg (sys.speedEscape cfg) = 0 := by
  rw [specificOrbitalEnergy, sys.speedEscape_sq cfg hr hG hM]
  ring

/-!
### D.3. Relation to the circular speed
-/

/-- The escape speed is `√2` times the circular speed at the same radius. -/
lemma speedEscape_eq_sqrt_two_mul_speedCircular (sys : VisViva) (cfg : ConfigurationSpace) :
    sys.speedEscape cfg = Real.sqrt 2 * sys.speedCircular cfg := by
  rw [speedEscape, speedCircular, ← Real.sqrt_mul (show (0 : ℝ) ≤ 2 by norm_num)]
  congr 1
  ring

/-- The square of the escape speed is twice the square of the circular speed. -/
lemma speedEscape_sq_eq_two_mul_speedCircular_sq (sys : VisViva) (cfg : ConfigurationSpace) :
    sys.speedEscape cfg ^ 2 = 2 * sys.speedCircular cfg ^ 2 := by
  rw [speedEscape_eq_sqrt_two_mul_speedCircular, mul_pow,
    Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

/-- A body on a circular orbit moves more slowly than the escape speed: it is bound. -/
lemma speedCircular_lt_speedEscape (sys : VisViva) (cfg : ConfigurationSpace) (hr : 0 < cfg.r)
    (hG : 0 < sys.G) (hM : 0 < sys.M) :
    sys.speedCircular cfg < sys.speedEscape cfg := by
  rw [speedCircular, speedEscape, Real.sqrt_lt_sqrt_iff (by positivity),
    show 2 * sys.G * sys.M / cfg.r = 2 * (sys.G * sys.M / cfg.r) by ring]
  have h : 0 < sys.G * sys.M / cfg.r := by positivity
  linarith

end VisViva
end ClassicalMechanics
