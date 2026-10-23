/-
Copyright (c) 2026 Rithwik Ranganathan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rithwik Ranganathan
-/
module

public import Mathlib.LinearAlgebra.CrossProduct
public import Physlib.ClassicalMechanics.HamiltonianMechanics.PoissonBracket
public import PhyslibAlpha.ClassicalMechanics.CentralForce.Basic
/-!

# Angular-momentum observables under a central force

Squared angular momentum, its axial component, and their Poisson brackets for central forces.

## i. Overview

The angular momentum of a particle at position `q` with momentum `p` is `L = q × p`. This file
defines it on phase space, together with the two functions of it which Poisson-commute: its squared
magnitude `L² = ‖L‖²` and its component `L_z` along the z-axis. Their gradients follow from
Lagrange's identity `‖q × p‖² = ⟪q, q⟫ ⟪p, p⟫ - ⟪q, p⟫²` and the explicit form
`L_z = q₀ p₁ - q₁ p₀`.

We show that `L²` and `L_z` are in involution, and that both Poisson-commute with any Hamiltonian
whose momentum gradient is parallel to the momentum and whose position gradient is parallel to the
position. By `CentralForce.hasGradientAt_hamiltonian_momentum` and
`CentralForce.hasGradientAt_hamiltonian_position`, this includes the Hamiltonian of every
central-force system away from the centre of force, so `L²` and `L_z` are conserved by the motion.

## ii. Key results

- `CentralForce.angularMomentum` : the angular momentum `L = q × p`.
- `CentralForce.angularMomentumSq`, `CentralForce.angularMomentumZ` : `L²` and `L_z`.
- `CentralForce.angularMomentumSq_eq` : Lagrange's identity for `L²`.
- `CentralForce.poissonBracket_angularMomentumSq_angularMomentumZ` : `{L², L_z} = 0`.
- `CentralForce.poissonBracket_angularMomentumSq_hamiltonian`,
  `CentralForce.poissonBracket_angularMomentumZ_hamiltonian` : `L²` and `L_z` Poisson-commute with
  the Hamiltonian of a central-force system.

## iii. Table of contents

- A. The angular momentum
  - A.1. The squared magnitude and the z-component
  - A.2. Smoothness
- B. Gradients
- C. Poisson brackets
  - C.1. The squared magnitude and the z-component are in involution
  - C.2. Poisson brackets for radial partial gradients
  - C.3. Conservation under a central force

## iv. References

* H. Goldstein, C. Poole and J. Safko, *Classical Mechanics*, 3rd edition,
  Section 9.7 (Poisson bracket relations for angular momentum) and Chapter 3 (central forces).
-/

@[expose] public section

namespace ClassicalMechanics

namespace CentralForce

open InnerProductSpace Matrix
open scoped ContDiff

/-!

## A. The angular momentum

-/

/-- The angular momentum `L = q × p` of a particle at position `q` with momentum `p`. -/
noncomputable def angularMomentum (p q : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 (q.ofLp ⨯₃ p.ofLp)

/-- The x-component of the angular momentum is `q₁ p₂ - q₂ p₁`. -/
lemma angularMomentum_apply_zero (p q : EuclideanSpace ℝ (Fin 3)) :
    angularMomentum p q 0 = q 1 * p 2 - q 2 * p 1 := by
  simp [angularMomentum, cross_apply]

/-- The y-component of the angular momentum is `q₂ p₀ - q₀ p₂`. -/
lemma angularMomentum_apply_one (p q : EuclideanSpace ℝ (Fin 3)) :
    angularMomentum p q 1 = q 2 * p 0 - q 0 * p 2 := by
  simp [angularMomentum, cross_apply]

/-- The z-component of the angular momentum is `q₀ p₁ - q₁ p₀`. -/
lemma angularMomentum_apply_two (p q : EuclideanSpace ℝ (Fin 3)) :
    angularMomentum p q 2 = q 0 * p 1 - q 1 * p 0 := by
  simp [angularMomentum, cross_apply]

/-!

### A.1. The squared magnitude and the z-component

-/

/-- The squared magnitude `L² = ‖q × p‖²` of the angular momentum, as a function on phase
space. -/
noncomputable def angularMomentumSq (p q : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  ‖angularMomentum p q‖ ^ 2

/-- The component `L_z` of the angular momentum along the z-axis, as a function on phase space. -/
noncomputable def angularMomentumZ (p q : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  angularMomentum p q 2

/-- The squared magnitude of the angular momentum is the sum of the squares of its components. -/
lemma angularMomentumSq_eq_sum (p q : EuclideanSpace ℝ (Fin 3)) :
    angularMomentumSq p q =
      angularMomentum p q 0 ^ 2 + angularMomentum p q 1 ^ 2 + angularMomentum p q 2 ^ 2 := by
  rw [angularMomentumSq, EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
  simp only [Real.norm_eq_abs, sq_abs]

/-- Lagrange's identity: the squared magnitude of the angular momentum `q × p` is
`⟪q, q⟫ ⟪p, p⟫ - ⟪q, p⟫²`. -/
lemma angularMomentumSq_eq (p q : EuclideanSpace ℝ (Fin 3)) :
    angularMomentumSq p q = ⟪q, q⟫_ℝ * ⟪p, p⟫_ℝ - ⟪q, p⟫_ℝ ^ 2 := by
  rw [angularMomentumSq_eq_sum, angularMomentum_apply_zero, angularMomentum_apply_one,
    angularMomentum_apply_two]
  simp only [PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial]
  ring

/-!

### A.2. Smoothness

-/

/-- The squared magnitude of the angular momentum is a smooth function on phase space. -/
lemma contDiff_angularMomentumSq : ContDiff ℝ ∞ (Function.uncurry angularMomentumSq) := by
  have h : Function.uncurry angularMomentumSq =
      fun x : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        ⟪x.2, x.2⟫_ℝ * ⟪x.1, x.1⟫_ℝ - ⟪x.2, x.1⟫_ℝ ^ 2 :=
    funext fun x => angularMomentumSq_eq x.1 x.2
  rw [h]
  exact ((contDiff_snd.inner ℝ contDiff_snd).mul (contDiff_fst.inner ℝ contDiff_fst)).sub
    ((contDiff_snd.inner ℝ contDiff_fst).pow 2)

/-- The z-component of the angular momentum is a smooth function on phase space. -/
lemma contDiff_angularMomentumZ : ContDiff ℝ ∞ (Function.uncurry angularMomentumZ) := by
  have h : Function.uncurry angularMomentumZ =
      fun x : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        x.2 0 * x.1 1 - x.2 1 * x.1 0 :=
    funext fun x => angularMomentum_apply_two x.1 x.2
  rw [h]
  fun_prop

/-!

## B. Gradients

-/

/-- The momentum gradient of `L²` is `2 ⟪q, q⟫ p - 2 ⟪q, p⟫ q`. -/
lemma hasGradientAt_angularMomentumSq_momentum (p q : EuclideanSpace ℝ (Fin 3)) :
    HasGradientAt (fun p' => angularMomentumSq p' q)
      ((2 * ⟪q, q⟫_ℝ) • p - (2 * ⟪q, p⟫_ℝ) • q) p := by
  simp only [angularMomentumSq_eq]
  convert ((hasGradientAt_inner_self p).const_mul ⟪q, q⟫_ℝ).sub
    ((hasDerivAt_pow 2 _).comp_hasGradientAt (hasGradientAt_inner_left q p)) using 1
  module

/-- The position gradient of `L²` is `2 ⟪p, p⟫ q - 2 ⟪q, p⟫ p`. -/
lemma hasGradientAt_angularMomentumSq_position (p q : EuclideanSpace ℝ (Fin 3)) :
    HasGradientAt (fun q' => angularMomentumSq p q')
      ((2 * ⟪p, p⟫_ℝ) • q - (2 * ⟪q, p⟫_ℝ) • p) q := by
  simp only [angularMomentumSq_eq]
  convert ((hasGradientAt_inner_self q).mul (hasGradientAt_const q ⟪p, p⟫_ℝ)).sub
    ((hasDerivAt_pow 2 _).comp_hasGradientAt (hasGradientAt_inner_right p q)) using 1
  module

/-- The momentum gradient of `L_z` is `q₀ e₁ - q₁ e₀`. -/
lemma hasGradientAt_angularMomentumZ_momentum (p q : EuclideanSpace ℝ (Fin 3)) :
    HasGradientAt (fun p' => angularMomentumZ p' q)
      (q 0 • EuclideanSpace.single 1 1 - q 1 • EuclideanSpace.single 0 1) p := by
  simp only [angularMomentumZ, angularMomentum_apply_two]
  exact ((hasGradientAt_coord 1 p).const_mul (q 0)).sub
    ((hasGradientAt_coord 0 p).const_mul (q 1))

/-- The position gradient of `L_z` is `p₁ e₀ - p₀ e₁`. -/
lemma hasGradientAt_angularMomentumZ_position (p q : EuclideanSpace ℝ (Fin 3)) :
    HasGradientAt (fun q' => angularMomentumZ p q')
      (p 1 • EuclideanSpace.single 0 1 - p 0 • EuclideanSpace.single 1 1) q := by
  simp only [angularMomentumZ, angularMomentum_apply_two]
  convert ((hasGradientAt_coord 0 q).mul (hasGradientAt_const q (p 1))).sub
    ((hasGradientAt_coord 1 q).mul (hasGradientAt_const q (p 0))) using 1
  module

/-!

## C. Poisson brackets

-/

/-!

### C.1. The squared magnitude and the z-component are in involution

-/

/-- The squared magnitude of the angular momentum and its z-component are in involution. -/
lemma poissonBracket_angularMomentumSq_angularMomentumZ (p q : EuclideanSpace ℝ (Fin 3)) :
    poissonBracket angularMomentumSq angularMomentumZ p q = 0 := by
  rw [poissonBracket_eq_of_hasGradientAt (hasGradientAt_angularMomentumSq_momentum p q)
    (hasGradientAt_angularMomentumSq_position p q) (hasGradientAt_angularMomentumZ_momentum p q)
    (hasGradientAt_angularMomentumZ_position p q)]
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_right,
    EuclideanSpace.inner_single_right, conj_trivial, PiLp.smul_apply, smul_eq_mul]
  ring

/-!

### C.2. Poisson brackets for radial partial gradients

At a phase-space point where the momentum gradient of a Hamiltonian is parallel to the momentum
and its position gradient is parallel to the position, its Poisson brackets with `L²` and `L_z`
vanish. These sufficient conditions apply to the central-force Hamiltonian away from the centre.

-/

/-- `L²` Poisson-commutes with any phase-space function whose momentum gradient is parallel to the
momentum and whose position gradient is parallel to the position. -/
lemma poissonBracket_angularMomentumSq_eq_zero_of_hasGradientAt
    {H : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    {p q : EuclideanSpace ℝ (Fin 3)} {a c : ℝ}
    (hp : HasGradientAt (fun p' => H p' q) (a • p) p)
    (hq : HasGradientAt (fun q' => H p q') (c • q) q) :
    poissonBracket angularMomentumSq H p q = 0 := by
  rw [poissonBracket_eq_of_hasGradientAt (hasGradientAt_angularMomentumSq_momentum p q)
    (hasGradientAt_angularMomentumSq_position p q) hp hq]
  simp only [inner_sub_left, real_inner_smul_left, real_inner_smul_right, real_inner_comm p q]
  ring

/-- `L_z` Poisson-commutes with any phase-space function whose momentum gradient is parallel to
the momentum and whose position gradient is parallel to the position. -/
lemma poissonBracket_angularMomentumZ_eq_zero_of_hasGradientAt
    {H : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    {p q : EuclideanSpace ℝ (Fin 3)} {a c : ℝ}
    (hp : HasGradientAt (fun p' => H p' q) (a • p) p)
    (hq : HasGradientAt (fun q' => H p q') (c • q) q) :
    poissonBracket angularMomentumZ H p q = 0 := by
  rw [poissonBracket_eq_of_hasGradientAt (hasGradientAt_angularMomentumZ_momentum p q)
    (hasGradientAt_angularMomentumZ_position p q) hp hq]
  simp only [inner_sub_left, real_inner_smul_left, real_inner_smul_right,
    EuclideanSpace.inner_single_left, conj_trivial]
  ring

/-!

### C.3. Conservation under a central force

-/

variable (S : CentralForce)

/-- Away from the centre of force, the squared magnitude of the angular momentum Poisson-commutes
with the Hamiltonian of a central-force system, so is conserved by the motion. -/
lemma poissonBracket_angularMomentumSq_hamiltonian (p : EuclideanSpace ℝ (Fin 3))
    {q : EuclideanSpace ℝ (Fin 3)} (hq : q ≠ 0) :
    poissonBracket angularMomentumSq S.hamiltonian p q = 0 :=
  poissonBracket_angularMomentumSq_eq_zero_of_hasGradientAt
    (S.hasGradientAt_hamiltonian_momentum p q) (S.hasGradientAt_hamiltonian_position p hq)

/-- Away from the centre of force, the z-component of the angular momentum Poisson-commutes with
the Hamiltonian of a central-force system, so is conserved by the motion. -/
lemma poissonBracket_angularMomentumZ_hamiltonian (p : EuclideanSpace ℝ (Fin 3))
    {q : EuclideanSpace ℝ (Fin 3)} (hq : q ≠ 0) :
    poissonBracket angularMomentumZ S.hamiltonian p q = 0 :=
  poissonBracket_angularMomentumZ_eq_zero_of_hasGradientAt
    (S.hasGradientAt_hamiltonian_momentum p q) (S.hasGradientAt_hamiltonian_position p hq)

end CentralForce

end ClassicalMechanics
