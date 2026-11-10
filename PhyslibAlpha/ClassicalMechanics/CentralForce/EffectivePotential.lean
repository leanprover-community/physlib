/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.ClassicalMechanics.CentralForce.AngularMomentum
/-!

# The effective potential of a central force

The radial momentum, the effective potential, and the reduction of central-force motion to a
one-dimensional radial problem.

## i. Overview

For a particle at position `q ≠ 0` with momentum `p`, the radial momentum `p_r = ⟪q, p⟫ / ‖q‖` is
the component of `p` along the position. By Lagrange's identity
`‖q × p‖² = ⟪q, q⟫ ⟪p, p⟫ - ⟪q, p⟫²`, the squared momentum splits into a radial part `p_r²` and an
angular part `L² / r²`, where `r = ‖q‖` and `L = ‖q × p‖`. The Hamiltonian of a central-force
system therefore becomes

$$H(p, q) = \frac{p_r^2}{2m} + V_{\mathrm{eff}}(L, r), \qquad
  V_{\mathrm{eff}}(L, r) = \frac{L^2}{2 m r^2} + V(r).$$

Since `L` is conserved (`CentralForce.poissonBracket_angularMomentumSq_hamiltonian`), this is the
Hamiltonian of a one-dimensional problem in the radial coordinate `r`, in which the centrifugal
barrier `L² / (2 m r²)` is added to the potential. The radial kinetic energy is non-negative, so
the motion is confined to the classically allowed region, where the effective potential is at most
the energy.

## ii. Key results

- `CentralForce.radialMomentum` : the radial momentum `p_r = ⟪q, p⟫ / ‖q‖`.
- `CentralForce.radialMomentum_sq_add_angularMomentumSq_div` : `p_r² + L² / r² = ⟪p, p⟫`.
- `CentralForce.effectivePotential` : the effective potential `L² / (2 m r²) + V(r)`.
- `CentralForce.hasDerivAt_effectivePotential` : its radial derivative `V'(r) - L² / (m r³)`.
- `CentralForce.hamiltonian_eq_effectivePotential` : `H = p_r² / (2 m) + V_eff(L, r)`.
- `CentralForce.effectivePotential_le_hamiltonian` : the effective potential at the position of the
  particle is at most its energy.

## iii. Table of contents

- A. The radial momentum
- B. The effective potential
  - B.1. Smoothness and the radial derivative
- C. The Hamiltonian in terms of the effective potential
  - C.1. The classically allowed region

## iv. References

* H. Goldstein, C. Poole and J. Safko, *Classical Mechanics*, 3rd edition, Section 3.3.
-/

@[expose] public section

namespace ClassicalMechanics

namespace CentralForce

open InnerProductSpace
open scoped ContDiff

/-!

## A. The radial momentum

-/

/-- The radial momentum `p_r = ⟪q, p⟫ / ‖q‖`, the component of the momentum `p` along the
position `q`. -/
noncomputable def radialMomentum (p q : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  ⟪q, p⟫_ℝ / ‖q‖

/-- Away from the centre of force, the squared momentum splits into the squared radial momentum
and the angular part `L² / r²`. -/
lemma radialMomentum_sq_add_angularMomentumSq_div (p : EuclideanSpace ℝ (Fin 3))
    {q : EuclideanSpace ℝ (Fin 3)} (hq : q ≠ 0) :
    radialMomentum p q ^ 2 + angularMomentumSq p q / ‖q‖ ^ 2 = ⟪p, p⟫_ℝ := by
  have hq' : ‖q‖ ≠ 0 := norm_ne_zero_iff.mpr hq
  rw [radialMomentum, angularMomentumSq_eq, real_inner_self_eq_norm_sq q]
  field_simp
  ring

/-!

## B. The effective potential

-/

variable (S : CentralForce)

/-- The effective potential `L² / (2 m r²) + V(r)` at radius `r` of a central-force system, for a
particle of angular momentum of magnitude `L`. The first term is the centrifugal barrier. -/
noncomputable def effectivePotential (L r : ℝ) : ℝ :=
  L ^ 2 / (2 * S.m * r ^ 2) + S.V r

/-!

### B.1. Smoothness and the radial derivative

-/

/-- The effective potential is smooth at positive radii. -/
lemma contDiffOn_effectivePotential (L : ℝ) :
    ContDiffOn ℝ ∞ (S.effectivePotential L) (Set.Ioi 0) := by
  refine ContDiffOn.add (contDiffOn_const.div (contDiffOn_const.mul (contDiffOn_id.pow 2))
    fun r hr => ?_) S.contDiffOn_V
  exact mul_ne_zero (mul_ne_zero two_ne_zero S.m_ne_zero) (pow_ne_zero 2 (ne_of_gt hr))

/-- At a positive radius `r`, the derivative of the effective potential is
`V'(r) - L² / (m r³)`, the negative of the sum of the force and the centrifugal force. -/
lemma hasDerivAt_effectivePotential (L : ℝ) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (S.effectivePotential L) (deriv S.V r - L ^ 2 / (S.m * r ^ 3)) r := by
  have h2mr : 2 * S.m * r ^ 2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero S.m_ne_zero) (pow_ne_zero 2 hr.ne')
  show HasDerivAt (fun r => L ^ 2 / (2 * S.m * r ^ 2) + S.V r) _ r
  convert ((hasDerivAt_const r (L ^ 2)).div ((hasDerivAt_pow 2 r).const_mul (2 * S.m))
    h2mr).add (S.hasDerivAt_V hr) using 1
  push_cast
  field_simp
  ring

/-!

## C. The Hamiltonian in terms of the effective potential

-/

/-- Away from the centre of force, the Hamiltonian of a central-force system is the radial kinetic
energy `p_r² / (2 m)` plus the effective potential at the radius `‖q‖`, for the magnitude
`‖q × p‖` of the angular momentum. -/
lemma hamiltonian_eq_effectivePotential (p : EuclideanSpace ℝ (Fin 3))
    {q : EuclideanSpace ℝ (Fin 3)} (hq : q ≠ 0) :
    S.hamiltonian p q =
      radialMomentum p q ^ 2 / (2 * S.m) + S.effectivePotential ‖angularMomentum p q‖ ‖q‖ := by
  have hq' : ‖q‖ ≠ 0 := norm_ne_zero_iff.mpr hq
  have hm := S.m_ne_zero
  rw [hamiltonian, effectivePotential, ← radialMomentum_sq_add_angularMomentumSq_div p hq,
    angularMomentumSq]
  field_simp
  ring

/-!

### C.1. The classically allowed region

-/

/-- Away from the centre of force, the effective potential at the position of the particle is at
most its energy: the motion is confined to the region where `V_eff(L, r) ≤ H`. -/
lemma effectivePotential_le_hamiltonian (p : EuclideanSpace ℝ (Fin 3))
    {q : EuclideanSpace ℝ (Fin 3)} (hq : q ≠ 0) :
    S.effectivePotential ‖angularMomentum p q‖ ‖q‖ ≤ S.hamiltonian p q := by
  rw [S.hamiltonian_eq_effectivePotential p hq]
  exact le_add_of_nonneg_left (div_nonneg (sq_nonneg _) (by linarith [S.m_pos]))

end CentralForce

end ClassicalMechanics
