/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.SpaceAndTime.SpaceTime.Basic
/-!

# A. Electromagnetism

Electromagnetism describes electric and magnetic fields, their potentials and sources, and the
relations between them on space and spacetime. This module provides a compact foundational API used
by more specialized electromagnetism modules in Physlib.

## A.1. Main definitions

The module contains coordinate-level types for electric and magnetic fields, a spacetime vector
potential, charge and current densities, and the constants describing an electromagnetic system.
For an `EMSystem`, it also defines the speed of light and Coulomb's constant in terms of the vacuum
permittivity and permeability.

## A.2. Current status

The definitions here are intentionally lightweight. More developed APIs are organized under the
`Kinematics`, `Dynamics`, `TemperedDistributional`, `ThreeDimension`, and `Vacuum` subdirectories.
The abbreviations in this file remain useful as shared entry points while those APIs continue to
converge.

## A.3. Future work

Charge and current densities should be generalized to signed measures while remaining convenient
for integration and tensor notation. As the specialized APIs stabilize, overlapping legacy
interfaces should be consolidated without breaking the physical meaning of existing declarations.

-/

@[expose] public section

namespace Electromagnetism

/-- The electric field is a map from `(d + 1)`-dimensional spacetime to `ℝ^d`. -/
abbrev ElectricField (d : ℕ := 3) := Time → Space d → EuclideanSpace ℝ (Fin d)

/-- The magnetic field is a map from `(d + 1)`-dimensional spacetime to `ℝ^d`. -/
abbrev MagneticField (d : ℕ := 3) := Time → Space d → EuclideanSpace ℝ (Fin d)

open realLorentzTensor

/-- The vector potential of an electromagnetic field. -/
abbrev VectorPotential (d : ℕ := 3) := SpaceTime d → ℝT[d, .up]

/-- The electric permittivity and the magnetic permeability of free space. -/
structure EMSystem where
  /-- The permittivity of free space. -/
  ε₀ : ℝ
  /-- The permeability of free space. -/
  μ₀ : ℝ

TODO "Charge density and current density should be generalized to signed measures,
  in such a way
  that they are still easy to work with and can be integrated with tensor notation.
  See here:
  https://leanprover.zulipchat.com/#narrow/channel/479953-Physlib/topic/Maxwell's.20Equations"

/-- The charge density. -/
abbrev ChargeDensity := Time → Space → ℝ

/-- The current density. -/
abbrev CurrentDensity := Time → Space → EuclideanSpace ℝ (Fin 3)

namespace EMSystem
variable (𝓔 : EMSystem)
open SpaceTime

/-- The speed of light. -/
noncomputable def c : ℝ := 1/(√(𝓔.μ₀ * 𝓔.ε₀))

/-- Coulomb's constant. -/
noncomputable def coulombConstant : ℝ := 1/(4 * Real.pi * 𝓔.ε₀)

end EMSystem

end Electromagnetism
