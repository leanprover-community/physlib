/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhysLean.Units.Basic
/-!
# Velocity

In this module we define the type `Velocity`, which represents the velocity of a particle
in `d`-dimensional space, in an arbitrary (but given) set of units.

-/

@[expose] public section
open Dimension
