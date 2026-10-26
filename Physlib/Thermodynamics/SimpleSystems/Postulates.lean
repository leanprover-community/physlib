/-
Copyright (c) 2026 Omar Aguilar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Omar Aguilar, Fabio Anza
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Physlib.Thermodynamics.SimpleSystems.WallsAndConstraints

/-!
# Thermodynamic postulates

Formulations of Callen's four postulates using equilibrium states and
constraints imposed by walls.

## i. Overview

Callen's four postulates specify the existence of equilibrium states,
entropy maximization as the criterion for equilibrium, and the
properties of entropy.

In this file, given a set of permitted combinations of internal energy,
volume, and component mole numbers, `Postulate1` asserts the existence
of an equilibrium state fully specified by one of those combinations.

`Postulate2` asserts that there exists a function (called entropy `S`)
of the subsystem equilibrium states in a composite system, with the
following property: when at least one internal constraint within a
closed composite system initially in equilibrium is removed, even if
other constraints are added, a final equilibrium state exists. Here, a
final state is in equilibrium (`IsEquilibrium`) if and only if
it satisfies `IsEntropyMaximum`: it maximizes `S` among the states of
the composite system that satisfy the final constraints imposed
by walls and have the same total internal energy, total volume, and
total mole number of each chemical component as the initial state.

`Postulate3` asserts that the entropy of a composite system is additive:
it equals the sum of its subsystem entropies. Also, it states that each
subsystem's entropy is continuous on its set of permitted coordinate
combinations, differentiable in the interior of that set, and increases
strictly monotonically with internal energy at fixed volume and
component mole numbers. It also requires the derivative of each subsystem's
entropy with respect to internal energy, at fixed volume and component mole
numbers, to be strictly positive in the interior of its set of permitted
coordinates.

`Postulate4` assumes an energy representation `U` of the entropy `S` and
asserts the following: the entropy vanishes when the partial derivative of
that system's internal energy with respect to its entropy, at fixed
volume and component mole numbers, is zero.

## ii. Key results

* `Postulate1`: existence of an equilibrium state.
* `IsEntropyMaximum`: entropy maximization under wall constraints
  and fixed global totals.
* `Postulate2`: characterization of initial and final equilibrium states
  by entropy maximization, and a guarantee that a final equilibrium state
  exists after internal constraint removal.
* `Postulate3`: entropy additivity, continuity, interior differentiability,
  strict increase with energy, and a strictly positive energy derivative
  in the interior.
* `Postulate4`: zero entropy condition in the energy representation.

## iii. Table of contents

- A. Postulate I: equilibrium states
- B. Postulate II: entropy maximization
- C. Postulate III: properties of entropy
- D. Postulate IV: zero entropy at zero temperature

## iv. References

Herbert B. Callen, *Thermodynamics and an Introduction to Thermostatistics*,
2nd edition, John Wiley & Sons, 1985. [ref: callen1985]

* Section 1.5, p. 13: Postulate I.
* Section 1.9, p. 26: closed composite systems and the release of internal constraints.
* Section 1.10, p. 27: Postulate II.
* Section 1.10, p. 28: Postulate III.
* Section 1.10, p. 29, Eq. (1.7): positivity of the entropy derivative
  with respect to internal energy.
* Section 1.10, p. 30: Postulate IV.
-/

@[expose] public section

namespace Thermodynamics

open scoped BigOperators

/-!
## A. Postulate I: equilibrium states
-/

/-- Postulate I: At least one equilibrium state exists with coordinates in `D`.
Each `EquilibriumState` is fully specified by its internal energy,
volume, and component mole numbers. -/
def Postulate1 {r : ℕ}
    (D : Set (StateCoordinates r)) : Prop :=
  Nonempty (EquilibriumState D)

/-!
## B. Postulate II: entropy maximization
-/

/-- The composite state `state_F` maximizes entropy `S` among the states
that satisfy the constraints determined by `walls` and `state_0`.
The argument `walls` specifies which quantities must remain fixed
for each collection of subsystems, and `state_0` supplies their fixed
values, as well as the total internal energy, total volume, and total
mole number of each chemical component that all these states must
preserve. The state `state_F` must itself satisfy these conditions.

Here, `D i` specifies the permitted coordinate combinations for
subsystem `i`. -/
def IsEntropyMaximum {r n : ℕ}
    {D : Fin n → Set (StateCoordinates r)}
    (S : CompositeState D → ℝ)
    (walls : Finset (Fin n) → Wall r)
    (state_0 state_F : CompositeState D) : Prop :=
  /- Given a composite state `state`, `satisfiesConstraints state`
     expresses the constraints it must satisfy, with `walls` specifying
     which kinds of quantities must remain fixed for each collection
     of subsystems and `state_0` supplying their fixed values and the
     global totals that must also be preserved. -/
  let satisfiesConstraints (state : CompositeState D) : Prop :=
    /- Require `state` to satisfy the constraints, with `walls` specifying
       which kinds of quantities must remain fixed for each collection of
       subsystems and `state_0` supplying their fixed values. -/
    Constraints walls state_0 state ∧
      /- Require the total internal energy to equal that of `state_0`. -/
      (∑ i, (state i).U) = (∑ i, (state_0 i).U) ∧
      /- Require the total volume to equal that of `state_0`. -/
      (∑ i, (state i).V) = (∑ i, (state_0 i).V) ∧
      /- Require the total mole number of each chemical component to equal
      that of `state_0`. -/
      (∀ j, (∑ i, (state i).N j) = (∑ i, (state_0 i).N j))
  /- Require the state `state_F` to satisfy these constraints. -/
  satisfiesConstraints state_F ∧
    /- Require every state satisfying these constraints to have entropy
     no greater than `S state_F`. -/
    ∀ state, satisfiesConstraints state → S state ≤ S state_F

/-- Postulate II: There exists an entropy function `S` such that, for
any constraints determined by `walls` and `state_0`, a composite state
`state_F` is in equilibrium (`IsEquilibrium walls state_0 state_F`)
if and only if it globally maximizes `S`, as specified by
`IsEntropyMaximum S walls state_0 state_F`.

For a closed composite system initially in equilibrium, removing at
least one constraint on a nonempty proper collection of subsystems,
even if other constraints are added, guarantees the existence of a final
equilibrium state under the final constraints. -/
def Postulate2 {r n : ℕ}
    {D : Fin n → Set (StateCoordinates r)}
    (IsEquilibrium : (Finset (Fin n) → Wall r) →
      CompositeState D → CompositeState D → Prop) : Prop :=
  ∃ S : CompositeState D → ℝ,
    /- For any constraints determined by `walls` and `state_0`, require
       the composite state `state_F` to be in equilibrium if and only if
       it maximizes entropy `S` subject to these constraints. -/
    (∀ walls state_0 state_F,
      IsEquilibrium walls state_0 state_F ↔
        IsEntropyMaximum S walls state_0 state_F) ∧
    (∀ (walls_0 walls_F : Finset (Fin n) → Wall r)
        (state_0 : CompositeState D),
      /- Assume the initial composite state `state_0` is in equilibrium under the
         constraints determined by `walls_0` and `state_0`. The first state argument
         supplies reference values; the second is the state assumed in equilibrium. -/
      IsEquilibrium walls_0 state_0 state_0 →
      /- Assume at least one internal constraint is removed: on a nonempty
         proper collection of subsystems, an energy, volume, or mole-number
         restriction holds initially but not finally. Other restrictions may
         be kept, removed, or added; their fixed values come from `state_0`. -/
      (∃ subsystems : Finset (Fin n),
        subsystems.Nonempty ∧
        subsystems ≠ Finset.univ ∧
        (((walls_0 subsystems).restrictsEnergy ∧
            ¬ (walls_F subsystems).restrictsEnergy) ∨
          ((walls_0 subsystems).restrictsVolume ∧
            ¬ (walls_F subsystems).restrictsVolume) ∨
          (∃ j, (walls_0 subsystems).restrictsMoleNumber j ∧
            ¬ (walls_F subsystems).restrictsMoleNumber j))) →
      /- Under these assumptions, require the existence of a final composite
         state `state_F` in equilibrium under the final constraints
         determined by `walls_F` and `state_0`. -/
      ∃ state_F, IsEquilibrium walls_F state_0 state_F)

/-!
## C. Postulate III: properties of entropy
-/

/-- The entropy `S state` of every composite state `state` equals the sum
of the entropies `S_subsystem i (state i)` of its subsystems. -/
def IsEntropyAdditive {r n : ℕ}
    {D : Fin n → Set (StateCoordinates r)}
    (S : CompositeState D → ℝ)
    (S_subsystem : (i : Fin n) → EquilibriumState (D i) → ℝ) : Prop :=
  /- Require the entropy `S state` of every composite state `state` to equal
     the sum of the subsystem entropies `S_subsystem i (state i)`. -/
  ∀ state, S state = ∑ i, S_subsystem i (state i)

/-- The entropy `S` admits a coordinate representation `S_coordinates` that is
differentiable within `D` at every point of `D` and agrees with `S` on every
equilibrium state. Its values outside `D` are unrestricted. -/
def IsEntropyDifferentiable {r : ℕ}
    {D : Set (StateCoordinates r)}
    (S : EquilibriumState D → ℝ) : Prop :=
  ∃ S_coordinates : StateCoordinates r → ℝ,
    DifferentiableOn ℝ S_coordinates D ∧
    ∀ state, S state = S_coordinates (state.U, state.V, state.N)


/-- The entropy `S` strictly increases with internal energy at fixed volume
and component mole numbers among equilibrium states with coordinates in `D`.
This compares entropy values and does not assert a strictly positive derivative. -/
def IsEntropyIncreasingInEnergy {r : ℕ}
    {D : Set (StateCoordinates r)}
    (S : EquilibriumState D → ℝ) : Prop :=
  ∀ state₁ state₂ : EquilibriumState D,
    state₁.V = state₂.V →
    state₁.N = state₂.N →
    state₁.U < state₂.U →
    S state₁ < S state₂

/-- The entropy `S` admits a coordinate representation whose derivative
with respect to internal energy is strictly positive at every equilibrium
state, at fixed volume and component mole numbers. -/
def IsEntropyEnergyDerivativePositive {r : ℕ}
    {D : Set (StateCoordinates r)}
    (S : EquilibriumState D → ℝ) : Prop :=
  ∃ S_coordinates : StateCoordinates r → ℝ,
    (∀ state, S state = S_coordinates (state.U, state.V, state.N)) ∧
    ∀ state : EquilibriumState D,
      0 < deriv (fun U => S_coordinates (U, state.V, state.N)) state.U

/-- The entropy `S` restricted to equilibrium states whose coordinates
lie in the interior of `D`. -/
def entropyOnInterior {r : ℕ}
    {D : Set (StateCoordinates r)}
    (S : EquilibriumState D → ℝ) :
    EquilibriumState (interior D) → ℝ :=
  fun state =>
    S ⟨state.U, state.V, state.N, interior_subset state.mem_domain⟩

/-- The entropy `S` admits a coordinate representation `S_coordinates` that is
continuous on `D`, including any boundary points belonging to `D`, and agrees
with `S` on every equilibrium state. -/
def IsEntropyContinuous {r : ℕ}
    {D : Set (StateCoordinates r)}
    (S : EquilibriumState D → ℝ) : Prop :=
  ∃ S_coordinates : StateCoordinates r → ℝ,
    ContinuousOn S_coordinates D ∧
    ∀ state, S state = S_coordinates (state.U, state.V, state.N)

/-- Postulate III: Composite entropy `S` is additive, and each subsystem
entropy `S_subsystem i` is continuous on its set `D i` of permitted coordinate
combinations, differentiable in its interior, and strictly increasing with
internal energy at fixed volume and component mole numbers. At interior
points, this derivative with respect to internal energy is strictly positive. -/
structure Postulate3 {r n : ℕ}
    {D : Fin n → Set (StateCoordinates r)}
    (S : CompositeState D → ℝ)
    (S_subsystem : (i : Fin n) → EquilibriumState (D i) → ℝ) : Prop where
  /-- Composite entropy is the sum of the subsystem entropies. -/
  additive : IsEntropyAdditive S S_subsystem
  /-- Each subsystem entropy is continuous on its domain `D i`. -/
  continuous : ∀ i, IsEntropyContinuous (S_subsystem i)
  /-- Each subsystem entropy is differentiable in the interior of its domain `D i`. -/
  differentiable : ∀ i,
    IsEntropyDifferentiable (entropyOnInterior (S_subsystem i))
  /-- Each subsystem entropy strictly increases with `U` at fixed `V` and `N`. -/
  increasingInEnergy : ∀ i, IsEntropyIncreasingInEnergy (S_subsystem i)
  /-- Each subsystem entropy has a positive energy derivative in the interior. -/
  positiveEnergyDerivative : ∀ i,
    IsEntropyEnergyDerivativePositive (entropyOnInterior (S_subsystem i))

/-!
## D. Postulate IV: zero entropy at zero temperature
-/

/-- The function `U` recovers the internal energy of every equilibrium state
`state` from its entropy `S state`, volume, and component mole numbers.
The identity is required only at coordinates attained by these states. -/
def IsEnergyRepresentation {r : ℕ}
    {D : Set (StateCoordinates r)}
    (S : EquilibriumState D → ℝ)
    (U : ℝ → ℝ → (Fin r → ℝ) → ℝ) : Prop :=
  ∀ state, U (S state) state.V state.N = state.U

/-- The set of entropy, volume, and component mole number combinations
attained by equilibrium states with coordinates in `D`. -/
def entropyCoordinateDomain {r : ℕ} {D : Set (StateCoordinates r)}
    (S : EquilibriumState D → ℝ) : Set (ℝ × ℝ × (Fin r → ℝ)) :=
  Set.range (fun state => (S state, state.V, state.N))

/-- Postulate IV: In the energy representation, zero temperature implies
zero entropy. Here, temperature is the derivative of internal energy `U`
with respect to entropy at fixed volume and component mole numbers.

The hypothesis `_h_rep` identifies `U` as an energy representation of `S`.
The derivative is taken within the set of entropy values attained at fixed
`V` and `N`. The implication applies to values in this set satisfying
`UniqueDiffWithinAt`. No limit as temperature tends to zero is asserted. -/
def Postulate4 {r : ℕ} {D : Set (StateCoordinates r)}
    (S : EquilibriumState D → ℝ)
    (U : ℝ → ℝ → (Fin r → ℝ) → ℝ)
    (_h_rep : IsEnergyRepresentation S U) : Prop :=
  ∀ (V : ℝ) (N : Fin r → ℝ),
    /- Let `allowed` be the set of attained entropy values at fixed `V` and `N`. -/
    let allowed : Set ℝ := {s | (s, V, N) ∈ entropyCoordinateDomain S}
    ∀ s ∈ allowed,
      /- Assume the condition ensuring uniqueness of derivatives within
         `allowed` at `s`. -/
      UniqueDiffWithinAt ℝ allowed s →
      /- If `U` has derivative zero with respect to entropy within `allowed`
         at `s`, require the entropy `s` to be zero. -/
      HasDerivWithinAt (fun s' => U s' V N) 0 allowed s →
      s = 0

end Thermodynamics
