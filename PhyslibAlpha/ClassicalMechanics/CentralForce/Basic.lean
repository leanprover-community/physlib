/-
Copyright (c) 2026 Rithwik Ranganathan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rithwik Ranganathan
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Physlib.Mathematics.Calculus.Gradient
/-!

# Central forces

Hamiltonian and partial gradients of a particle in a conservative central potential.

## i. Overview

This file models a particle of mass `m` in three-dimensional space under a conservative central
force centred at the origin. The force is derived from a potential `V (‖q‖)` which depends only on
the distance `‖q‖` from the origin. Its Hamiltonian, as a function of the momentum `p` and the
position `q`, is

$$H(p, q) = \frac{\langle p, p\rangle}{2m} + V(\|q\|).$$

The Kepler problem, `V r = -k / r`, and the isotropic harmonic oscillator, `V r = k r² / 2`, are
the most important examples.

The radial potential `V` is represented by a function on all of `ℝ`, with smoothness required
only for positive radii. Its value at zero is part of this total-function representation; the
position-gradient and smoothness results apply only when `q ≠ 0`, allowing potentials singular
at the physical centre.

This file defines the Hamiltonian and computes its partial gradients: the momentum gradient is the
velocity `p / m`, and away from the centre the position gradient `V'(‖q‖) q / ‖q‖` is parallel to
the position. The latter is what makes the angular momentum a conserved quantity.

## ii. Key results

- `CentralForce` : the input data, a mass and a potential smooth away from the centre of force.
- `CentralForce.hamiltonian` : the Hamiltonian.
- `CentralForce.hasGradientAt_hamiltonian_momentum`,
  `CentralForce.hasGradientAt_hamiltonian_position` : its partial gradients.
- `CentralForce.contDiffOn_hamiltonian` : it is smooth away from the centre of force.

## iii. Table of contents

- A. The input data
- B. The Hamiltonian
  - B.1. Gradients of the Hamiltonian
  - B.2. Smoothness of the Hamiltonian

## iv. References

* H. Goldstein, C. Poole and J. Safko, *Classical Mechanics*, 3rd edition, Chapter 3.
-/

@[expose] public section

namespace ClassicalMechanics

open InnerProductSpace
open scoped ContDiff

/-!

## A. The input data

-/

/-- A particle in three-dimensional space under a conservative central force centred at the origin,
specified by its mass `m` and a radial potential `V` smooth at positive radii. -/
structure CentralForce where
  /-- The mass of the particle. -/
  m : ℝ
  /-- The potential, as a function of the distance from the centre of force. -/
  V : ℝ → ℝ
  /-- The mass of the particle is positive. -/
  m_pos : 0 < m
  /-- The potential is smooth away from the centre of force. -/
  contDiffOn_V : ContDiffOn ℝ ∞ V (Set.Ioi 0)

namespace CentralForce

variable (S : CentralForce)

/-- The mass of the particle is non-zero. -/
@[simp]
lemma m_ne_zero : S.m ≠ 0 := S.m_pos.ne'

/-!

## B. The Hamiltonian

-/

/-- The Hamiltonian `H(p, q) = ⟪p, p⟫ / (2 m) + V ‖q‖` of a central-force system, as a function of
the momentum `p` and the position `q`. -/
noncomputable def hamiltonian (p q : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  (1 / (2 * S.m)) * ⟪p, p⟫_ℝ + S.V ‖q‖

/-!

### B.1. Gradients of the Hamiltonian

-/

/-- The momentum gradient of the Hamiltonian of a central-force system is the velocity `p / m`. -/
lemma hasGradientAt_hamiltonian_momentum (p q : EuclideanSpace ℝ (Fin 3)) :
    HasGradientAt (fun p' => S.hamiltonian p' q) (S.m⁻¹ • p) p := by
  show HasGradientAt (fun p' => (1 / (2 * S.m)) * ⟪p', p'⟫_ℝ + S.V ‖q‖) _ p
  convert ((hasGradientAt_inner_self p).const_mul (1 / (2 * S.m))).add
    (hasGradientAt_const p (S.V ‖q‖)) using 1
  module

/-- Away from the centre of force, the position gradient of the Hamiltonian of a central-force
system is `V'(‖q‖) q / ‖q‖`, which is parallel to the position. -/
lemma hasGradientAt_hamiltonian_position (p : EuclideanSpace ℝ (Fin 3))
    {q : EuclideanSpace ℝ (Fin 3)} (hq : q ≠ 0) :
    HasGradientAt (fun q' => S.hamiltonian p q') ((deriv S.V ‖q‖ / ‖q‖) • q) q := by
  have hV : HasDerivAt S.V (deriv S.V ‖q‖) ‖q‖ :=
    ((S.contDiffOn_V.differentiableOn (by simp)).differentiableAt
      (Ioi_mem_nhds (norm_pos_iff.mpr hq))).hasDerivAt
  show HasGradientAt (fun q' => (1 / (2 * S.m)) * ⟪p, p⟫_ℝ + S.V ‖q'‖) _ q
  convert (hasGradientAt_const q ((1 / (2 * S.m)) * ⟪p, p⟫_ℝ)).add
    (hV.comp_hasGradientAt (hasGradientAt_norm hq)) using 1
  rw [zero_add, smul_smul, div_eq_mul_inv]

/-!

### B.2. Smoothness of the Hamiltonian

-/

/-- The Hamiltonian of a central-force system is smooth away from the centre of force. -/
lemma contDiffOn_hamiltonian :
    ContDiffOn ℝ ∞ (Function.uncurry S.hamiltonian) {x | x.2 ≠ 0} := by
  have hnorm : ContDiffOn ℝ ∞
      (fun x : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) => ‖x.2‖) {x | x.2 ≠ 0} :=
    fun x hx => ((contDiffAt_norm ℝ hx).comp x contDiffAt_snd).contDiffWithinAt
  have hkin : ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      (1 / (2 * S.m)) * ⟪x.1, x.1⟫_ℝ) :=
    contDiff_const.mul (contDiff_fst.inner ℝ contDiff_fst)
  exact hkin.contDiffOn.add (S.contDiffOn_V.comp hnorm fun x hx => norm_pos_iff.mpr hx)

end CentralForce

end ClassicalMechanics
