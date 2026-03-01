/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Electromagnetism.Dynamics.IsExtrema
import PhysLean.SpaceAndTime.Space.Norm
import PhysLean.SpaceAndTime.Space.Translations
import PhysLean.SpaceAndTime.Space.ConstantSliceDist
import PhysLean.SpaceAndTime.TimeAndSpace.ConstantTimeDist
/-!
# The electrostatics of a circular coil

## i. Overview

This module is currently a stub, but will eventually contain the electrostatics of a
circular coil carrying a steady current. The references below have in them statements of the
electromagnetic potentials and fields around a circular coil.

## ii. Key results

## iii. Table of contents

- A. The current density

## iv. References

- https://ntrs.nasa.gov/api/citations/20140002333/downloads/20140002333.pdf

-/

TODO "TCGIW" "Copying the structure of the electrostatics of an infinite wire,
  complete the definitions and proofs for a circular coil carrying a steady current."

namespace Electromagnetism
namespace DistElectromagneticPotential
open minkowskiMatrix SpaceTime SchwartzMap Lorentz
attribute [-simp] Fintype.sum_sum_type
attribute [-simp] Nat.succ_eq_add_one
/-!

## A. The current density

-/
end DistElectromagneticPotential
end Electromagnetism
