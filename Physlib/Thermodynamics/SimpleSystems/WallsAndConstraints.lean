/-
Copyright (c) 2026 Omar Aguilar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Omar Aguilar, Fabio Anza
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Physlib.Thermodynamics.SimpleSystems.EquilibriumState

/-!
# Thermodynamic walls and constraints

Wall restrictions on individual subsystems, groups of subsystems, and the
whole composite system; constraints relating initial and final composite
states.

## i. Overview

We consider the initial and final states of a composite system, with each
subsystem internally in equilibrium in both composite states. The walls of
a composite system specify which individual subsystem
coordinates or sums of subsystem coordinates must retain their initial
values in the final state. For a collection of subsystems bounded by walls,
the total internal energy is the sum of the subsystem internal energies, the
total volume is the sum of their volumes, and the total mole number of each
chemical component is the sum of that component's mole numbers in those subsystems.

In this file, `Wall r` records which kinds of quantities are required to
be held fixed: total internal energy, total volume, and the total mole
number of each of the `r` chemical components. The function `walls`
specifies a `Wall r` for each finite collection of subsystems.

`Constraints walls state_0 state_F` states that whenever `walls` requires
a quantity to be held fixed for a collection of subsystems, its total for
that collection is the same in the initial composite state `state_0`
and the final composite state `state_F`. This allows constraints imposed by
walls to be expressed in the same way for a collection containing a single
subsystem, several subsystems, or all subsystems of the composite system.

## ii. Key results

* `Wall r`: records which kinds of quantities must be held fixed.
* `Constraints`: expresses the equalities between initial and final
  totals for each collection of subsystems, as required by `walls`.

## iii. Table of contents

- A. Walls
- B. Constraints

## iv. References

Herbert B. Callen, *Thermodynamics and an Introduction to Thermostatistics*,
2nd edition, John Wiley & Sons, 1985. [ref: callen1985]

* Section 1.6, pp. 15–16: restrictive and nonrestrictive walls.
* Section 1.7, p. 17: walls restrictive with respect to energy, volume, and the mole numbers.
* Section 1.9, p. 26: composite systems, closed systems and internal constraints.
-/

@[expose] public section

namespace Thermodynamics

/-!
## A. Walls
-/

/-- Records which kinds of quantities are required to be held fixed:
total internal energy, total volume, and the total mole number of each
of the `r` chemical components. -/
structure Wall (r : ℕ) where
  /-- Whether the total internal energy is required to be held fixed. -/
  restrictsEnergy : Prop
  /-- Whether the total volume is required to be held fixed. -/
  restrictsVolume : Prop
  /-- For each chemical component, whether its total mole number is
  required to be held fixed. -/
  restrictsMoleNumber : Fin r → Prop

open scoped BigOperators

/-!
## B. Constraints
-/

/-- Specifies that whenever `walls` requires a quantity to be held fixed
for a collection of subsystems, its total for that collection is the same
in the initial composite state `state_0` and the final composite state
`state_F`. The quantities considered are internal energy, volume, and
the mole number of each chemical component.

Here `n` is the number of subsystems, `r` is the number of chemical
components, and `D i` is the admissible coordinate domain of subsystem
`i`. The function `walls` specifies a `Wall r` for each finite collection
of subsystems. Both composite states use the same subsystem domains `D`.

Each implication `→` requires equal initial and final totals when the
wall condition on its left is true. If that condition is false, that
implication imposes no equality. When `subsystems = Finset.univ`, the
collection includes all subsystems, so the sums give the totals for the
composite system as a whole.

When `subsystems = Finset.univ`, the implications impose the equalities
required by `walls Finset.univ` between the initial and final totals
for the whole composite system. -/

def Constraints {r n : ℕ}
    {D : Fin n → Set (StateCoordinates r)}
    (walls : Finset (Fin n) → Wall r)
    (state_0 state_F : CompositeState D) : Prop :=
  /- For every collection of subsystems, if `walls` requires its total
     internal energy to be held fixed, the sum of their final internal
     energies must equal the sum of their initial internal energies.
     The same applies to volume and to each chemical component's mole
     number whenever `walls` requires that total to be held fixed. -/
  ∀ subsystems,
    ((walls subsystems).restrictsEnergy →
      (∑ i ∈ subsystems, (state_F i).U) =
        ∑ i ∈ subsystems, (state_0 i).U) ∧
    ((walls subsystems).restrictsVolume →
      (∑ i ∈ subsystems, (state_F i).V) =
        ∑ i ∈ subsystems, (state_0 i).V) ∧
    (∀ j, (walls subsystems).restrictsMoleNumber j →
      (∑ i ∈ subsystems, (state_F i).N j) =
        ∑ i ∈ subsystems, (state_0 i).N j)

end Thermodynamics
