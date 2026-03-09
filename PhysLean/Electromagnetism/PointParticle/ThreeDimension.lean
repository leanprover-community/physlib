/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhysLean.Electromagnetism.Dynamics.IsExtrema
public import PhysLean.SpaceAndTime.Space.Norm
public import PhysLean.SpaceAndTime.Space.Translations
public import PhysLean.SpaceAndTime.TimeAndSpace.ConstantTimeDist
/-!

# Electrostatics of a stationary point particle in 3d

## i. Overview

In this module we give the electromagnetic properties of a point particle
sitting at the origin in 3d space.

## ii. Key results

- `threeDimPointParticle` : The electromagnetic potential of a point particle
  stationary at a point in 3d space.
- `threeDimPointParticle_isExterma` : The electric field of a point
  particle stationary at a point of 3d space satisfies Maxwell's equations

## iii. Table of contents

- A. The current density
  - A.1. The charge density
  - A.2. The 3-current density
- B. The Potentials
  - B.1. The electromagnetic potential
  - B.2. The scalar potential
  - B.3. The vector potential is zero
- C. The electric field
  - C.1. the time derivative of the electric field
- D. The magnetic field
- E. Maxwell's equations

## iv. References

-/

@[expose] public section

namespace Electromagnetism
open Distribution SchwartzMap
open Space MeasureTheory
namespace DistElectromagneticPotential

/-!

## A. The current density

The current density of a point particle in 3d space is given by:

$$J(r) = (c q \delta(r - r₀), 0, 0, 0) $$

where $c$ is the speed light, $q$ is the charge of the particle and $r₀$ is the position of the
particle in 3d space.

-/

/-- The current density of a point particle stationary at a point `r₀`
  of 3d space. -/
noncomputable def threeDimPointParticleCurrentDensity (c : SpeedOfLight) (q : ℝ) (r₀ : Space 3) :
    DistLorentzCurrentDensity 3 := (SpaceTime.distTimeSlice c).symm <|
  constantTime ((c * q) • diracDelta' ℝ r₀ (Lorentz.Vector.basis (Sum.inl 0)))

lemma threeDimPointParticleCurrentDensity_eq_distTranslate (c : SpeedOfLight) (q : ℝ)
    (r₀ : Space 3) :
    threeDimPointParticleCurrentDensity c q r₀ = ((SpaceTime.distTimeSlice c).symm <|
    constantTime <|
    distTranslate (basis.repr r₀) <|
    ((c * q) • diracDelta' ℝ 0 (Lorentz.Vector.basis (Sum.inl 0)))) := by
  rw [threeDimPointParticleCurrentDensity]
  congr
  ext η
  simp [distTranslate_apply]

/-!

### A.1. The charge density

The charge density of a point particle in 3d space is given by:
$$ρ(r) = q \delta(r - r₀) $$

where $q$ is the charge of the particle and $r₀$ is the position of the particle in 3d space.

-/

@[simp]
lemma threeDimPointParticleCurrentDensity_chargeDensity (c : SpeedOfLight) (q : ℝ) (r₀ : Space 3) :
    (threeDimPointParticleCurrentDensity c q r₀).chargeDensity c =
    constantTime (q • diracDelta ℝ r₀) := by
  ext ε
  simp only [DistLorentzCurrentDensity.chargeDensity, one_div, Lorentz.Vector.temporalCLM,
    Fin.isValue, threeDimPointParticleCurrentDensity, map_smul, LinearMap.coe_mk, AddHom.coe_mk,
    ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearMap.coe_smul',
    ContinuousLinearMap.coe_comp', LinearMap.coe_toContinuousLinearMap', Pi.smul_apply,
    Function.comp_apply, constantTime_apply, diracDelta'_apply, Lorentz.Vector.apply_smul,
    Lorentz.Vector.basis_apply, ↓reduceIte, mul_one, smul_eq_mul, diracDelta_apply]
  field_simp

/-!

### A.2. The 3-current density

The 3-current density of a point particle in 3d space is given by:
$$\vec J(r) = 0.$$

In other words, there is no current flow for a point particle at rest.

-/

@[simp]
lemma threeDimPointParticleCurrentDensity_currentDensity (c : SpeedOfLight) (q : ℝ) (r₀ : Space 3) :
    (threeDimPointParticleCurrentDensity c q r₀).currentDensity c = 0 := by
  ext ε i
  simp [threeDimPointParticleCurrentDensity, DistLorentzCurrentDensity.currentDensity,
    Lorentz.Vector.spatialCLM, constantTime_apply]

/-!

## B. The Potentials

-/

/-!

### B.1. The electromagnetic potential

The 4-potential of a point particle in 3d space is given by:

$$A(r) = \frac{q μ₀ c}{4 π |r - r₀|} (1, 0, 0, 0) $$

where $μ₀$ is the permeability of free space, $c$ is the speed of light,
$q$ is the charge of the particle and $r₀$ is the position of the particle in 3d space.

-/
open Real

/-- The electromagnetic potential of a point particle stationary at `r₀`
  of 3d space. -/
noncomputable def threeDimPointParticle (𝓕 : FreeSpace) (q : ℝ) (r₀ : Space 3) :
    DistElectromagneticPotential 3 := (SpaceTime.distTimeSlice 𝓕.c).symm <| Space.constantTime <|
  distOfFunction (fun x => (((q * 𝓕.μ₀ * 𝓕.c)/ (4 * π)) * ‖x - r₀‖⁻¹) •
    Lorentz.Vector.basis (Sum.inl 0))
    (((IsDistBounded.inv_shift _).const_mul_fun _).smul_const _)

lemma threeDimPointParticle_eq_distTranslate (𝓕 : FreeSpace) (q : ℝ) (r₀ : Space 3) :
    threeDimPointParticle 𝓕 q r₀ = ((SpaceTime.distTimeSlice 𝓕.c).symm <|
    constantTime <|
    distTranslate (basis.repr r₀) <|
    distOfFunction (fun x => (((q * 𝓕.μ₀ * 𝓕.c)/ (4 * π))* ‖x‖⁻¹) •
      Lorentz.Vector.basis (Sum.inl 0))
      ((IsDistBounded.inv.const_mul_fun _).smul_const _)) := by
  rw [threeDimPointParticle]
  congr
  ext η
  simp [distTranslate_ofFunction]

/-!

### B.2. The scalar potential

The first component of the 4-potential is the scalar potential, once
one has taken account of factors of the speed of light. It is given by:

$$V(r) = \frac{q}{4 π \epsilon_0 |r - r_0|}.$$

-/

lemma threeDimPointParticle_scalarPotential (𝓕 : FreeSpace) (q : ℝ) (r₀ : Space 3) :
    (threeDimPointParticle 𝓕 q r₀).scalarPotential 𝓕.c =
    Space.constantTime (distOfFunction (fun x => (q/ (4 * π * 𝓕.ε₀))• ‖x - r₀‖⁻¹)
      (((IsDistBounded.inv_shift _).const_mul_fun _))) := by
  ext ε
  simp only [scalarPotential, Lorentz.Vector.temporalCLM, Fin.isValue, map_smul,
    ContinuousLinearMap.comp_smulₛₗ, ringHom_apply, threeDimPointParticle, LinearMap.coe_mk,
    AddHom.coe_mk, ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearMap.coe_smul',
    ContinuousLinearMap.coe_comp', LinearMap.coe_toContinuousLinearMap', Pi.smul_apply,
    Function.comp_apply, constantTime_apply, distOfFunction_vector_eval, Lorentz.Vector.apply_smul,
    Lorentz.Vector.basis_apply, ↓reduceIte, mul_one, smul_eq_mul]
  rw [distOfFunction_mul_fun _ (IsDistBounded.inv_shift _),
    distOfFunction_mul_fun _ (IsDistBounded.inv_shift _)]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, ContinuousLinearMap.coe_smul', Pi.smul_apply,
    smul_eq_mul]
  ring_nf
  simp only [𝓕.c_sq, one_div, mul_inv_rev, mul_eq_mul_right_iff, inv_eq_zero, OfNat.ofNat_ne_zero,
    or_false]
  field_simp

/-!

### B.3. The vector potential is zero

The spatial components of the 4-potential give the vector potential, which is zero
for a stationary point particle.

$$\vec A(r) = 0.$$

-/

@[simp]
lemma threeDimPointParticle_vectorPotential (𝓕 : FreeSpace) (q : ℝ) (r₀ : Space 3) :
    (threeDimPointParticle 𝓕 q r₀).vectorPotential 𝓕.c = 0 := by
  ext ε i
  simp [vectorPotential, Lorentz.Vector.spatialCLM,
    threeDimPointParticle, constantTime_apply, distOfFunction_vector_eval]

/-!

## C. The electric field

The electric field of a point particle in 3d space is given by:
$$\vec E(r) = \frac{q}{4 π \epsilon_0} \frac{\vec r - \vec r₀}{|\vec r - \vec r₀|^3}.$$

-/

lemma threeDimPointParticle_electricField (𝓕 : FreeSpace) (q : ℝ) (r₀ : Space 3) :
    (threeDimPointParticle 𝓕 q r₀).electricField 𝓕.c =
    (q/ (4 * π * 𝓕.ε₀)) • constantTime (distOfFunction (fun x : Space 3 =>
      ‖x - r₀‖ ^ (- 3 : ℤ) • basis.repr (x - r₀))
      ((IsDistBounded.zpow_smul_repr_self (- 3 : ℤ) (by omega)).comp_sub_right r₀)) := by
  simp only [electricField, LinearMap.coe_mk, AddHom.coe_mk, threeDimPointParticle_scalarPotential,
    smul_eq_mul, threeDimPointParticle_vectorPotential, map_zero, sub_zero, Int.reduceNeg, zpow_neg]
  rw [constantTime_distSpaceGrad, distOfFunction_mul_fun _
    (IsDistBounded.inv_shift r₀)]
  simp only [map_smul]
  trans -(q / (4 * π * 𝓕.ε₀)) • (constantTime <| distGrad <| distTranslate (basis.repr r₀) <|
    (distOfFunction (fun x => ‖x‖⁻¹) (IsDistBounded.inv)))
  · simp [distTranslate_ofFunction]
  rw [Space.distTranslate_distGrad]
  have := Space.distGrad_distOfFunction_norm_zpow (d := 2) (-1) (by grind)
  simp_all [distOfFunction_neg, distTranslate_ofFunction]

/-!

### C.1. the time derivative of the electric field

-/

@[simp]
lemma threeDimPointParticle_electricField_timeDeriv (𝓕 : FreeSpace) (q : ℝ) (r₀ : Space 3) :
    Space.distTimeDeriv ((threeDimPointParticle 𝓕 q r₀).electricField 𝓕.c) = 0 := by
  rw [threeDimPointParticle_electricField]
  simp

/-!

## D. The magnetic field

Given that the vector potential is zero, the magnetic field is also zero.

-/

@[simp]
lemma threeDimPointParticle_magneticFieldMatrix (q : ℝ) (r₀ : Space 3) :
    (threeDimPointParticle 𝓕 q r₀).magneticFieldMatrix 𝓕.c = 0 := by
  ext η
  simp [magneticFieldMatrix_eq_vectorPotential]

/-!

## E. Maxwell's equations

The divergence of the electric field of a point particle in 3d space is given by:
$$∇ · \vec E(r) = \frac{1}{\epsilon_0} q \delta(r - r₀).$$

From this, it follows that the electromagnetic potential of a point particle in 3d space
satisfies Maxwell's equations for a point particle at rest.

-/

lemma threeDimPointParticle_div_electricField {𝓕} (q : ℝ) (r₀ : Space 3) :
    distSpaceDiv ((threeDimPointParticle 𝓕 q r₀).electricField 𝓕.c) =
    (1/𝓕.ε₀) • constantTime (q • diracDelta ℝ r₀) := by
  rw [threeDimPointParticle_electricField]
  simp only [Int.reduceNeg, zpow_neg, map_smul, smul_smul]
  have h1 := Space.distDiv_inv_pow_eq_dim (d := 2)
  simp at h1
  trans (q / (4 * π * 𝓕.ε₀)) •
    distSpaceDiv (constantTime <|
    distTranslate (basis.repr r₀) <|
    (distOfFunction (fun x => ‖x‖ ^ (-3 : ℤ) • basis.repr x)
      (IsDistBounded.zpow_smul_repr_self (- 3 : ℤ) (by omega))))
  · ext η
    simp [distTranslate_ofFunction]
  simp only [Int.reduceNeg, zpow_neg, one_div]
  rw [constantTime_distSpaceDiv, distDiv_distTranslate, h1]
  simp only [map_smul, smul_smul]
  ext η
  simp [constantTime_apply, diracDelta_apply, distTranslate_apply]
  left
  ring_nf
  field_simp

lemma threeDimPointParticle_isExterma (𝓕 : FreeSpace) (q : ℝ) (r₀ : Space 3) :
    (threeDimPointParticle 𝓕 q r₀).IsExtrema 𝓕 (threeDimPointParticleCurrentDensity 𝓕.c q r₀) := by
  rw [isExtrema_iff_components]
  apply And.intro
  · intro ε
    rw [gradLagrangian_sum_inl_0]
    simp only [one_div, mul_inv_rev, threeDimPointParticleCurrentDensity_chargeDensity, map_smul,
      ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul]
    rw [threeDimPointParticle_div_electricField]
    simp only [one_div, map_smul, ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul]
    field_simp
    simp [𝓕.c_sq]
    right
    field_simp
    simp
  · intro ε i
    rw [gradLagrangian_sum_inr_i]
    simp

end DistElectromagneticPotential
end Electromagnetism
