/-
Copyright (c) 2026 Omar Aguilar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Omar Aguilar, Fabio Anza
-/
module

public import Mathlib.Basic.Real.Basic

/-!
# Thermodynamic equilibrium states

State coordinates, equilibrium states, and states of composite systems.

## i. Overview

The equilibrium state of a simple macroscopic system is specified by its
internal energy `U`, volume `V`, and mole numbers `N` of its `r` chemical
components. A composite system consists of two or more simple systems, called
subsystems.

In this file, `StateCoordinates r` represents the tuple of coordinates
`(U, V, N)` of a simple macroscopic system with `r` chemical components in
equilibrium. Here, `U` and `V` are real numbers, and `N : Fin r → ℝ` assigns a
mole number to each chemical component. `EquilibriumState D` represents an
equilibrium state of a simple system specified by the coordinates `(U, V, N)` in
the domain `D`. This domain specifies the values that these coordinates can
take. `CompositeState D` represents the equilibrium states of the subsystems in a
composite system, where each subsystem `i` has an equilibrium state whose
coordinates belong to the domain `D i`.

## ii. Key results

The file introduces three definitions:

* `StateCoordinates`: the coordinates `(U, V, N)`.
* `EquilibriumState`: an equilibrium state whose coordinates belong to an
  admissible domain.
* `CompositeState`: the equilibrium states of the subsystems in a composite
  system, with a domain for each subsystem.

## iii. Table of contents

- A. State coordinates
- B. Equilibrium states
- C. Composite states

## iv. References

Herbert B. Callen, *Thermodynamics and an Introduction to Thermostatistics*,
2nd edition, John Wiley & Sons, 1985. [ref: callen1985]

* Section 1.5, p. 13: equilibrium states
* Section 1.9, p. 26: composite systems.
-/

@[expose] public section

namespace Thermodynamics

/-!
## A. State coordinates
-/

/-- State coordinates `(U, V, N)` for a simple system with `r` chemical components.
Internal energy, volume, and the mole numbers `N i` are represented by real numbers. -/
abbrev StateCoordinates (r : ℕ) : Type :=
  ℝ × ℝ × (Fin r → ℝ)

/-!
## B. Equilibrium states
-/

/-- An equilibrium state specified by coordinates `(U, V, N)` in the admissible domain `D`.
Physical restrictions on the coordinates, such as positive volume, can be imposed through `D`. -/
@[ext]
structure EquilibriumState {r : ℕ}
    (D : Set (StateCoordinates r)) where
  /-- Internal energy. -/
  U : ℝ
  /-- Volume. -/
  V : ℝ
  /-- Mole numbers of the chemical components. -/
  N : Fin r → ℝ
  /-- The coordinates belong to the admissible domain. -/
  mem_domain : (U, V, N) ∈ D

/-!
## C. Composite states
-/

/-- A configuration of `n` subsystems, each internally in equilibrium and belonging to its
own admissible domain `D i`. The subsystems share the component index type `Fin r`.
Mutual equilibrium between subsystems is not required. -/
abbrev CompositeState {r n : ℕ}
    (D : Fin n → Set (StateCoordinates r)) : Type :=
  (i : Fin n) → EquilibriumState (D i)

end Thermodynamics
