/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhysLean.Units.WithDim.Velocity
public import PhysLean.Units.WithDim.Mass
public import PhysLean.Units.WithDim.Basic
/-!
# Momentum

In this module we define the type `Momentum`, which represents the momentum of a particle
in `d`-dimensional space, in an arbitrary (but given) set of units.

-/

@[expose] public section
open Dimension

/-- Momentum in `d`-dimensional space in an arbitrary, but given, set of units.
  In `(3+1)d` space time this corresponds to `3`-momentum not `4`-momentum. -/
abbrev Momentum (d : ℕ := 3) : Type := WithDim (M𝓭 * L𝓭 * T𝓭⁻¹) (Fin d → ℝ)
