/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Electromagnetism.Dynamics.IsExtrema
import PhysLean.SpaceAndTime.Space.Norm
import PhysLean.SpaceAndTime.Space.Translations
import PhysLean.SpaceAndTime.TimeAndSpace.ConstantTimeDist
/-!

# The electrostatics of a stationary point particle in 1d

## i. Overview

In this module we give the electromagnetic properties of a point particle
sitting at the origin in 1d space.

## ii. Key results

- `oneDimPointParticle` : The electromagnetic potential of a point particle
  stationary at the origin of 1d space.
- `oneDimPointParticle_isExterma` : The electric field of a point
  particle stationary at the origin of 1d space satisfies Maxwell's equations

## iii. Table of contents

- A. The current density
- B. The Potentials
  - B.1. The electromagnetic potential
  - B.2. The vector potential is zero
  - B.3. The scalar potential
- C. The electric field
  - C.1. The time derivative of the electric field
- D. The magnetic field
- E. Maxwell's equations

## iv. References

-/

namespace Electromagnetism
open Distribution SchwartzMap
open Space MeasureTheory
namespace DistElectromagneticPotential

/-!

## A. The current density

-/

/-- The current density of a point particle stationary at the origin
  of 1d space. -/
noncomputable def oneDimPointParticleCurrentDensity (c : SpeedOfLight) (q : ℝ) (r₀ : Space 1) :
    DistLorentzCurrentDensity 1 := (SpaceTime.distTimeSlice c).symm <|
  constantTime ((c * q) • diracDelta' ℝ r₀ (Lorentz.Vector.basis (Sum.inl 0)))

lemma oneDimPointParticleCurrentDensity_eq_distTranslate (c : SpeedOfLight) (q : ℝ) (r₀ : Space 1) :
    oneDimPointParticleCurrentDensity c q r₀ = ((SpaceTime.distTimeSlice c).symm <|
    constantTime <|
    distTranslate (basis.repr r₀) <|
    ((c * q) • diracDelta' ℝ 0 (Lorentz.Vector.basis (Sum.inl 0)))) := by
  rw [oneDimPointParticleCurrentDensity]
  congr
  ext η
  simp [distTranslate_apply]

@[simp]
lemma oneDimPointParticleCurrentDensity_currentDensity (c : SpeedOfLight) (q : ℝ) (r₀ : Space 1) :
    (oneDimPointParticleCurrentDensity c q r₀).currentDensity c = 0 := by
  ext ε i
  simp [oneDimPointParticleCurrentDensity, DistLorentzCurrentDensity.currentDensity,
    Lorentz.Vector.spatialCLM, constantTime_apply]

@[simp]
lemma oneDimPointParticleCurrentDensity_chargeDensity (c : SpeedOfLight) (q : ℝ) (r₀ : Space 1) :
    (oneDimPointParticleCurrentDensity c q r₀).chargeDensity c =
    constantTime (q • diracDelta ℝ r₀) := by
  ext ε
  simp only [DistLorentzCurrentDensity.chargeDensity, one_div, Lorentz.Vector.temporalCLM,
    Fin.isValue, oneDimPointParticleCurrentDensity, map_smul, LinearMap.coe_mk, AddHom.coe_mk,
    ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearMap.coe_smul',
    ContinuousLinearMap.coe_comp', LinearMap.coe_toContinuousLinearMap', Pi.smul_apply,
    Function.comp_apply, constantTime_apply, diracDelta'_apply, Lorentz.Vector.apply_smul,
    Lorentz.Vector.basis_apply, ↓reduceIte, mul_one, smul_eq_mul, diracDelta_apply]
  field_simp

/-!

## B. The Potentials

-/

/-!

### B.1. The electromagnetic potential

-/

/-- The electromagnetic potential of a point particle stationary at `r₀`
  of 1d space. -/
noncomputable def oneDimPointParticle (𝓕 : FreeSpace) (q : ℝ) (r₀ : Space 1) :
    DistElectromagneticPotential 1 := (SpaceTime.distTimeSlice 𝓕.c).symm <| Space.constantTime <|
  distOfFunction (fun x => ((- (q * 𝓕.μ₀ * 𝓕.c)/ 2) * ‖x - r₀‖) • Lorentz.Vector.basis (Sum.inl 0))
    (by fun_prop)

lemma oneDimPointParticle_eq_distTranslate (𝓕 : FreeSpace) (q : ℝ) (r₀ : Space 1) :
    oneDimPointParticle 𝓕 q r₀ = ((SpaceTime.distTimeSlice 𝓕.c).symm <|
    constantTime <|
    distTranslate (basis.repr r₀) <|
    distOfFunction (fun x => ((- (q * 𝓕.μ₀ * 𝓕.c)/ 2) * ‖x‖) • Lorentz.Vector.basis (Sum.inl 0))
      (by fun_prop)) := by
  rw [oneDimPointParticle]
  congr
  ext η
  simp [distTranslate_ofFunction]

/-

### B.2. The vector potential is zero

-/

@[simp]
lemma oneDimPointParticle_vectorPotential (𝓕 : FreeSpace) (q : ℝ) (r₀ : Space 1) :
    (oneDimPointParticle 𝓕 q r₀).vectorPotential 𝓕.c = 0 := by
  ext ε i
  simp [vectorPotential, Lorentz.Vector.spatialCLM,
    oneDimPointParticle, constantTime_apply, distOfFunction_vector_eval]

/-!

### B.3. The scalar potential

-/

lemma oneDimPointParticle_scalarPotential (𝓕 : FreeSpace) (q : ℝ) (r₀ : Space 1) :
    (oneDimPointParticle 𝓕 q r₀).scalarPotential 𝓕.c =
    Space.constantTime (distOfFunction (fun x =>
      - ((q * 𝓕.μ₀ * 𝓕.c ^ 2)/(2)) • ‖x-r₀‖) (by fun_prop)) := by
  ext ε
  simp only [scalarPotential, Lorentz.Vector.temporalCLM, Fin.isValue, map_smul,
    ContinuousLinearMap.comp_smulₛₗ, Real.ringHom_apply, oneDimPointParticle, LinearMap.coe_mk,
    AddHom.coe_mk, ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearMap.coe_smul',
    ContinuousLinearMap.coe_comp', LinearMap.coe_toContinuousLinearMap', Pi.smul_apply,
    Function.comp_apply, constantTime_apply, distOfFunction_vector_eval, Lorentz.Vector.apply_smul,
    Lorentz.Vector.basis_apply, ↓reduceIte, mul_one, smul_eq_mul, neg_mul]
  rw [distOfFunction_mul_fun _ (by fun_prop), distOfFunction_neg,
    distOfFunction_mul_fun _ (by fun_prop)]
  simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul,
    ContinuousLinearMap.neg_apply]
  ring

/-!

## C. The electric field

-/

lemma oneDimPointParticle_electricField (𝓕 : FreeSpace) (q : ℝ) (r₀ : Space 1) :
    (oneDimPointParticle 𝓕 q r₀).electricField 𝓕.c =
    ((q * 𝓕.μ₀ * 𝓕.c ^ 2) / 2) • constantTime (distOfFunction (fun x : Space 1 =>
      ‖x - r₀‖ ^ (- 1 : ℤ) • basis.repr (x - r₀))
      ((IsDistBounded.zpow_smul_repr_self (- 1 : ℤ) (by omega)).comp_sub_right r₀)) := by
  have h1 := Space.distGrad_distOfFunction_norm_zpow (d := 0) 1 (by grind)
  simp at h1
  simp only [electricField, LinearMap.coe_mk, AddHom.coe_mk, oneDimPointParticle_scalarPotential,
    smul_eq_mul, neg_mul, oneDimPointParticle_vectorPotential, map_zero, sub_zero, Int.reduceNeg,
    zpow_neg, zpow_one]
  rw [constantTime_distSpaceGrad, distOfFunction_neg, distOfFunction_mul_fun _ (by fun_prop)]
  simp only [map_neg, map_smul, neg_neg]
  congr
  trans distGrad <| distTranslate (basis.repr r₀) <| (distOfFunction (fun x => ‖x‖) (by fun_prop))
  · ext1 η
    simp [distTranslate_ofFunction]
  rw [Space.distTranslate_distGrad]
  simp [h1, distTranslate_ofFunction]

/-!

### C.1. The time derivative of the electric field

-/

@[simp]
lemma oneDimPointParticle_electricField_timeDeriv (𝓕 : FreeSpace) (q : ℝ) (r₀ : Space 1) :
    Space.distTimeDeriv ((oneDimPointParticle 𝓕 q r₀).electricField 𝓕.c) = 0 := by
  rw [oneDimPointParticle_electricField]
  simp

/-!

## D. The magnetic field

-/

lemma oneDimPointParticle_magneticFieldMatrix (q : ℝ) (r₀ : Space 1) :
    (oneDimPointParticle 𝓕 q r₀).magneticFieldMatrix 𝓕.c = 0 := by
  simp

/-!

## E. Maxwell's equations

-/

lemma oneDimPointParticle_div_electricField {𝓕} (q : ℝ) (r₀ : Space 1) :
    distSpaceDiv ((oneDimPointParticle 𝓕 q r₀).electricField 𝓕.c) =
    (𝓕.μ₀ * 𝓕.c ^ 2) • constantTime (q • diracDelta ℝ r₀) := by
  rw [oneDimPointParticle_electricField]
  simp only [Int.reduceNeg, zpow_neg, zpow_one, map_smul, smul_smul]
  have h1 := Space.distDiv_inv_pow_eq_dim (d := 0)
  simp at h1
  trans (q * 𝓕.μ₀ * 𝓕.c.val ^ 2 / 2) •
    distSpaceDiv (constantTime <|
    distTranslate (basis.repr r₀) <|
    (distOfFunction (fun x => ‖x‖ ^ (-1 : ℤ) • basis.repr x)
      (IsDistBounded.zpow_smul_repr_self (- 1 : ℤ) (by omega))))
  · ext η
    simp [distTranslate_ofFunction]
  simp only [Int.reduceNeg, zpow_neg, zpow_one]
  rw [constantTime_distSpaceDiv, distDiv_distTranslate, h1]
  simp only [map_smul]
  suffices h : volume.real (Metric.ball (0 : Space 1) 1) = 2 by
    rw [h]
    simp [smul_smul]
    ext η
    simp [constantTime_apply, diracDelta_apply, distTranslate_apply]
    left
    ring_nf
  simp [MeasureTheory.Measure.real]
  rw [InnerProductSpace.volume_ball_of_dim_odd (k := 0)]
  · simp
  · simp

lemma oneDimPointParticle_isExterma (𝓕 : FreeSpace) (q : ℝ) (r₀ : Space 1) :
    (oneDimPointParticle 𝓕 q r₀).IsExtrema 𝓕 (oneDimPointParticleCurrentDensity 𝓕.c q r₀) := by
  rw [isExtrema_iff_components]
  apply And.intro
  · intro ε
    rw [gradLagrangian_sum_inl_0]
    simp only [one_div, mul_inv_rev, oneDimPointParticleCurrentDensity_chargeDensity, map_smul,
      ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul]
    rw [oneDimPointParticle_div_electricField]
    simp only [map_smul, ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  · intro ε i
    rw [gradLagrangian_sum_inr_i]
    simp

end DistElectromagneticPotential
end Electromagnetism
