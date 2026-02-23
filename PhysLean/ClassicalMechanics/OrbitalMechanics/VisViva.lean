/-
Copyright (c) 2026 Hannah Dawe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hannah Dawe
-/

import Mathlib.Data.Real.Basic

/-!
# Circular Orbit Vis Viva
Defines the orbital speed for a circular orbit (v^2 = G M / r).
-/

namespace ClassicalMechanics

structure VisViva where
  G : ℝ      -- gravitational constant
  M : ℝ      -- central mass body
  m : ℝ      -- orbiting mass body # for later usage

namespace VisViva

structure ConfigurationSpace where
  r : ℝ      -- radius

/-- Orbital speed for a circular orbit. -/
def speedCircular (sys : VisViva) (cfg : ConfigurationSpace) : ℝ :=
  Real.sqrt (sys.G * sys.M / cfg.r)

/-- Lemma: the square of the circular orbit speed equals G M / r. -/
lemma speedCircular_sq (sys : VisViva) (cfg : ConfigurationSpace) (hr : cfg.r > 0) :
    (speedCircular sys cfg)^2 = sys.G * sys.M / cfg.r := by
  simp [speedCircular, Real.sqrt_sq hr.le]

end VisViva
end ClassicalMechanics

