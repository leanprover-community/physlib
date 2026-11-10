/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.ClassicalMechanics.CentralForce.AngularMomentum
/-!

# The Laplace–Runge–Lenz vector

The Laplace–Runge–Lenz vector of the Kepler problem, its geometry, its magnitude and its
conservation.

## i. Overview

For a particle of mass `m` in the Kepler potential `V r = -k / r`, the Laplace–Runge–Lenz vector is

$$A = p \times L - m k \frac{q}{\|q\|},$$

where `L = q × p` is the angular momentum. Unlike the angular momentum, which is conserved for
every central force, the Runge–Lenz vector is conserved only for the inverse-square law. It is the
extra conserved quantity responsible for the closed elliptical orbits of the Kepler problem, and,
in quantum mechanics, for the accidental degeneracy of the hydrogen spectrum.

This file defines `A` for an arbitrary central-force system with a coupling constant `k`, and
shows:

- `A` is orthogonal to `L`, so lies in the plane of the orbit;
- `⟪A, q⟫ = L² - m k ‖q‖`, which, writing `θ` for the angle between `A` and `q`, is the orbit
  equation `‖q‖ (m k + ‖A‖ cos θ) = L²` of a conic section;
- `‖A‖² = (m k)² + 2 m H L²` when the potential is the Kepler potential, so that the
  eccentricity `‖A‖ / (m k)` of the orbit is fixed by the energy and the angular momentum;
- every component of `A` Poisson-commutes with the Kepler Hamiltonian away from the centre of
  force, so `A` is conserved by the motion.

## ii. Key results

- `CentralForce.rungeLenz` : the Laplace–Runge–Lenz vector.
- `CentralForce.rungeLenz_eq` : its expansion `⟪p, p⟫ q - ⟪q, p⟫ p - (m k / ‖q‖) q`.
- `CentralForce.inner_rungeLenz_angularMomentum` : it is orthogonal to the angular momentum.
- `CentralForce.inner_rungeLenz_position` : the orbit equation.
- `CentralForce.norm_rungeLenz_sq` : its squared magnitude in terms of the energy and `L²`.
- `CentralForce.poissonBracket_inner_rungeLenz_hamiltonian` : it is conserved under the Kepler
  potential.

## iii. Table of contents

- A. The Laplace–Runge–Lenz vector
- B. Geometry of the orbit
- C. The magnitude
- D. Conservation
  - D.1. Gradients of the components
  - D.2. Poisson brackets with the Kepler Hamiltonian

## iv. References

* H. Goldstein, C. Poole and J. Safko, *Classical Mechanics*, 3rd edition, Section 3.9.
-/

@[expose] public section

namespace ClassicalMechanics

namespace CentralForce

open InnerProductSpace Matrix

variable (S : CentralForce)

/-!

## A. The Laplace–Runge–Lenz vector

-/

/-- The Laplace–Runge–Lenz vector `A = p × L - m k q / ‖q‖` of a central-force system with
coupling constant `k`, as a function of the momentum `p` and the position `q`, where `L = q × p` is
the angular momentum. It is conserved when the potential is the Kepler potential `-k / r`. -/
noncomputable def rungeLenz (k : ℝ) (p q : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 (p.ofLp ⨯₃ (angularMomentum p q).ofLp) - (S.m * k / ‖q‖) • q

/-- The Laplace–Runge–Lenz vector is `⟪p, p⟫ q - ⟪q, p⟫ p - (m k / ‖q‖) q`. -/
lemma rungeLenz_eq (k : ℝ) (p q : EuclideanSpace ℝ (Fin 3)) :
    S.rungeLenz k p q = ⟪p, p⟫_ℝ • q - ⟪q, p⟫_ℝ • p - (S.m * k / ‖q‖) • q := by
  rw [rungeLenz, momentum_cross_angularMomentum]

/-!

## B. Geometry of the orbit

-/

/-- The Laplace–Runge–Lenz vector is orthogonal to the angular momentum, so lies in the plane of
the orbit. -/
lemma inner_rungeLenz_angularMomentum (k : ℝ) (p q : EuclideanSpace ℝ (Fin 3)) :
    ⟪S.rungeLenz k p q, angularMomentum p q⟫_ℝ = 0 := by
  simp [rungeLenz_eq, inner_sub_left, real_inner_smul_left, inner_position_angularMomentum,
    inner_momentum_angularMomentum]

/-- The orbit equation `⟪A, q⟫ = L² - m k ‖q‖`. Writing `θ` for the angle between the
Laplace–Runge–Lenz vector `A` and the position `q`, it reads `‖q‖ (m k + ‖A‖ cos θ) = L²`, the
equation of a conic section with a focus at the centre of force. -/
lemma inner_rungeLenz_position (k : ℝ) (p q : EuclideanSpace ℝ (Fin 3)) :
    ⟪S.rungeLenz k p q, q⟫_ℝ = angularMomentumSq p q - S.m * k * ‖q‖ := by
  rw [rungeLenz_eq, angularMomentumSq_eq]
  simp only [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
    real_inner_comm p q]
  rcases eq_or_ne ‖q‖ 0 with hq | hq
  · simp [hq, sq]
  · field_simp

/-!

## C. The magnitude

-/

/-- Away from the centre of force, for the Kepler potential `V r = -k / r` the squared magnitude
of the Laplace–Runge–Lenz vector is `(m k)² + 2 m H L²`, where `H` is the energy. -/
lemma norm_rungeLenz_sq {k : ℝ} (hV : Set.EqOn S.V (fun r => -k / r) (Set.Ioi 0))
    (p : EuclideanSpace ℝ (Fin 3)) {q : EuclideanSpace ℝ (Fin 3)} (hq : q ≠ 0) :
    ‖S.rungeLenz k p q‖ ^ 2 =
      (S.m * k) ^ 2 + 2 * S.m * S.hamiltonian p q * angularMomentumSq p q := by
  have hr : ‖q‖ ≠ 0 := norm_ne_zero_iff.mpr hq
  rw [← real_inner_self_eq_norm_sq, rungeLenz_eq, hamiltonian, angularMomentumSq_eq,
    hV (Set.mem_Ioi.mpr (norm_pos_iff.mpr hq))]
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
    real_inner_comm p q]
  simp only [real_inner_self_eq_norm_sq]
  field_simp
  ring

/-!

## D. Conservation

The component `⟪A, n⟫` of the Laplace–Runge–Lenz vector along a fixed vector `n` is a function on
phase space. We compute its partial gradients, and show that it Poisson-commutes with the
Hamiltonian of the Kepler problem.

-/

/-!

### D.1. Gradients of the components

-/

/-- The momentum gradient of the component `⟪A, n⟫` of the Laplace–Runge–Lenz vector is
`2 ⟪q, n⟫ p - ⟪p, n⟫ q - ⟪q, p⟫ n`. -/
lemma hasGradientAt_inner_rungeLenz_momentum (k : ℝ) (n p q : EuclideanSpace ℝ (Fin 3)) :
    HasGradientAt (fun p' => ⟪S.rungeLenz k p' q, n⟫_ℝ)
      ((2 * ⟪q, n⟫_ℝ) • p - ⟪p, n⟫_ℝ • q - ⟪q, p⟫_ℝ • n) p := by
  simp only [rungeLenz_eq, inner_sub_left, real_inner_smul_left]
  convert (((hasGradientAt_inner_self p).mul (hasGradientAt_const p ⟪q, n⟫_ℝ)).sub
    ((hasGradientAt_inner_left q p).mul (hasGradientAt_inner_right n p))).sub
    (hasGradientAt_const p (S.m * k / ‖q‖ * ⟪q, n⟫_ℝ)) using 1
  module

/-- Away from the centre of force, the position gradient of the component `⟪A, n⟫` of the
Laplace–Runge–Lenz vector is `⟪p, p⟫ n - ⟪p, n⟫ p - m k (n / ‖q‖ - ⟪q, n⟫ q / ‖q‖ ^ 3)`. -/
lemma hasGradientAt_inner_rungeLenz_position (k : ℝ) (n p : EuclideanSpace ℝ (Fin 3))
    {q : EuclideanSpace ℝ (Fin 3)} (hq : q ≠ 0) :
    HasGradientAt (fun q' => ⟪S.rungeLenz k p q', n⟫_ℝ)
      (⟪p, p⟫_ℝ • n - ⟪p, n⟫_ℝ • p - (S.m * k) • (‖q‖⁻¹ • n - (⟪q, n⟫_ℝ / ‖q‖ ^ 3) • q)) q := by
  have hr : ‖q‖ ≠ 0 := norm_ne_zero_iff.mpr hq
  -- the gradient of `q' ↦ ⟪q', n⟫ / ‖q'‖`, the component of the unit vector along `n`
  have hu : HasGradientAt (fun q' => ‖q'‖⁻¹ * ⟪q', n⟫_ℝ)
      (‖q‖⁻¹ • n - (⟪q, n⟫_ℝ / ‖q‖ ^ 3) • q) q := by
    convert ((hasDerivAt_inv hr).comp_hasGradientAt (hasGradientAt_norm hq)).mul
      (hasGradientAt_inner_right n q) using 1
    rw [smul_smul, smul_smul, sub_eq_add_neg, ← neg_smul]
    congr 2
    field_simp
  have h := (((hasGradientAt_inner_right n q).const_mul ⟪p, p⟫_ℝ).sub
    ((hasGradientAt_inner_right p q).mul (hasGradientAt_const q ⟪p, n⟫_ℝ))).sub
    (hu.const_mul (S.m * k))
  convert h using 1
  · funext q'
    simp only [rungeLenz_eq, inner_sub_left, real_inner_smul_left]
    ring
  · module

/-!

### D.2. Poisson brackets with the Kepler Hamiltonian

-/

/-- Conservation of the Laplace–Runge–Lenz vector: away from the centre of force, every component
`⟪A, n⟫` of the Laplace–Runge–Lenz vector Poisson-commutes with the Hamiltonian of a central-force
system with the Kepler potential `V r = -k / r`, so is conserved by the motion. -/
theorem poissonBracket_inner_rungeLenz_hamiltonian {k : ℝ}
    (hV : Set.EqOn S.V (fun r => -k / r) (Set.Ioi 0)) (n p : EuclideanSpace ℝ (Fin 3))
    {q : EuclideanSpace ℝ (Fin 3)} (hq : q ≠ 0) :
    poissonBracket (fun p' q' => ⟪S.rungeLenz k p' q', n⟫_ℝ) S.hamiltonian p q = 0 := by
  have hr : ‖q‖ ≠ 0 := norm_ne_zero_iff.mpr hq
  rw [poissonBracket_eq_of_hasGradientAt (f := fun p' q' => ⟪S.rungeLenz k p' q', n⟫_ℝ)
    (S.hasGradientAt_inner_rungeLenz_momentum k n p q)
    (S.hasGradientAt_inner_rungeLenz_position k n p hq) (S.hasGradientAt_hamiltonian_momentum p q)
    (S.hasGradientAt_hamiltonian_position_of_eqOn_kepler hV p hq)]
  simp only [inner_sub_left, real_inner_smul_left, real_inner_smul_right,
    real_inner_self_eq_norm_sq, real_inner_comm p q, real_inner_comm p n, real_inner_comm q n]
  field_simp
  ring

end CentralForce

end ClassicalMechanics
