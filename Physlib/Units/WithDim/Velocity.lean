/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Thierfelder, Joseph Tooby-Smith
-/
module

public import Physlib.Units.WithDim.Basic
/-!
# Velocity

In this module we define the type `Velocity`, which represents the velocity of a particle
in `d`-dimensional space, in an arbitrary (but given) set of units.

-/

@[expose] public section

open Dimension

/-- The velocity of a particle in `d`-dimensional space in an arbitrary, but given, set of units:
  `d` real components carrying the dimension of a length over a time. In `(3+1)d` space time this
  is the `3`-velocity, not the `4`-velocity. -/
abbrev Velocity (d : ℕ := 3) : Type := WithDim (L𝓭 * T𝓭⁻¹) (Fin d → ℝ)
