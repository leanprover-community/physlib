/-
Copyright (c) 2026 Rithwik Ranganathan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rithwik Ranganathan
-/
module

public import PhyslibAlpha.ClassicalMechanics.CentralForce.AngularMomentum
/-!
# Conserved quantities for central forces

The Hamiltonian, squared angular momentum, and axial angular momentum as a family of observables.

## i. Overview

The central-force Hamiltonian and the squared magnitude and axial component of angular momentum
form a family of three observables. Their Poisson brackets vanish away from the centre of force,
and their phase-space gradients are given by the existing central-force results.

## ii. Key results

- `CentralForce.conservedQuantities` : the three observables.
- `CentralForce.poissonBracket_conservedQuantities` : the observables are pairwise in involution.
- `CentralForce.gradient_conservedQuantities` : the phase-space gradients of the observables.

## iii. Table of contents

- A. The conserved quantities
  - A.1. Involution
  - A.2. Gradients

## iv. References

See `PhyslibAlpha.ClassicalMechanics.CentralForce.AngularMomentum` for references.
-/

@[expose] public section

namespace ClassicalMechanics.CentralForce

open InnerProductSpace
open scoped ContDiff

/-!

## A. The conserved quantities

-/

variable (S : CentralForce)

/-- The three conserved quantities in involution of a central-force system: the Hamiltonian `H`,
the squared magnitude `L²` of the angular momentum, and its z-component `L_z`. -/
noncomputable def conservedQuantities :
    Fin 3 → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ :=
  ![S.hamiltonian, angularMomentumSq, angularMomentumZ]

/-!

### A.1. Involution

-/

/-- Away from the centre of force, the conserved quantities of a central-force system are pairwise
in involution. -/
lemma poissonBracket_conservedQuantities (i j : Fin 3) (p : EuclideanSpace ℝ (Fin 3))
    {q : EuclideanSpace ℝ (Fin 3)} (hq : q ≠ 0) :
    poissonBracket (S.conservedQuantities i) (S.conservedQuantities j) p q = 0 := by
  have hSqH := S.poissonBracket_angularMomentumSq_hamiltonian p hq
  have hZH := S.poissonBracket_angularMomentumZ_hamiltonian p hq
  have hSqZ := poissonBracket_angularMomentumSq_angularMomentumZ p q
  have hHSq : poissonBracket S.hamiltonian angularMomentumSq p q = 0 := by
    rw [poissonBracket_antisymm, hSqH, neg_zero]
  have hHZ : poissonBracket S.hamiltonian angularMomentumZ p q = 0 := by
    rw [poissonBracket_antisymm, hZH, neg_zero]
  have hZSq : poissonBracket angularMomentumZ angularMomentumSq p q = 0 := by
    rw [poissonBracket_antisymm, hSqZ, neg_zero]
  fin_cases i <;> fin_cases j <;> simp [conservedQuantities, poissonBracket_self, *]

/-!

### A.2. Gradients

-/

/-- Away from the centre of force, the phase-space gradients of the conserved quantities of a
central-force system. -/
lemma gradient_conservedQuantities (p : EuclideanSpace ℝ (Fin 3)) {q : EuclideanSpace ℝ (Fin 3)}
    (hq : q ≠ 0) :
    (fun i => (gradient (fun p' => S.conservedQuantities i p' q) p,
      gradient (fun q' => S.conservedQuantities i p q') q)) =
    ![(S.m⁻¹ • p, (deriv S.V ‖q‖ / ‖q‖) • q),
      ((2 * ⟪q, q⟫_ℝ) • p - (2 * ⟪q, p⟫_ℝ) • q, (2 * ⟪p, p⟫_ℝ) • q - (2 * ⟪q, p⟫_ℝ) • p),
      (q 0 • EuclideanSpace.single 1 1 - q 1 • EuclideanSpace.single 0 1,
        p 1 • EuclideanSpace.single 0 1 - p 0 • EuclideanSpace.single 1 1)] := by
  funext i
  fin_cases i
  · exact Prod.ext (S.hasGradientAt_hamiltonian_momentum p q).gradient
      (S.hasGradientAt_hamiltonian_position p hq).gradient
  · exact Prod.ext (hasGradientAt_angularMomentumSq_momentum p q).gradient
      (hasGradientAt_angularMomentumSq_position p q).gradient
  · exact Prod.ext (hasGradientAt_angularMomentumZ_momentum p q).gradient
      (hasGradientAt_angularMomentumZ_position p q).gradient


end ClassicalMechanics.CentralForce
