/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Thierfelder, Joseph Tooby-Smith
-/
module

public import Physlib.Units.WithDim.Basic
/-!
# Mass

In this module we define the type `Mass`, which represents the mass of a particle,
in an arbitrary (but given) set of units.

-/

@[expose] public section

open Dimension

/-- The mass of a particle in an arbitrary, but given, set of units: a real number carrying the
  dimension of mass. -/
abbrev Mass : Type := WithDim M𝓭 ℝ
