/-
Copyright (c) 2026 Tom Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.HarmonicOscillator.LadderSystem
public import Physlib.Mathematics.InnerProductSpace.Gaussian
/-!

# A vacuum state for the harmonic oscillator

An explicit Gaussian vacuum for the d-dimensional harmonic oscillator ladder system.

## i. Overview

For a `d`-dimensional oscillator `Q`, `vacuumGaussian` is the Gaussian
`exp(-∑ᵢ(xᵢ/ξᵢ)²/2)`, rescaled coordinatewise by the characteristic lengths `ξᵢ` through the
diagonal continuous linear equivalence `diagEquiv`. Every annihilation operator kills this
Schwartz function, so `hasVacuum_vacuumGaussian` supplies a `LadderSystem.HasVacuum` witness
without an isotropy assumption.

The isotropic unit-length case (`Q.ξ i = 1` for all `i`) is represented by
`stdGaussian (Space d) ℂ`, the function `x ↦ exp(-‖x‖²/2)` from
`Physlib.Mathematics.InnerProductSpace.Gaussian`.
`hasVacuum_stdGaussian_of_forall_xi_eq_one` derives the unit-length case from `vacuumGaussian`.
The theorem `loweringCLM_stdGaussian_of_xi_eq_one` assumes unit length only in the selected
mode, so it is proved separately.

## ii. Key results

- `diagEquiv` : the diagonal rescaling of `Space d` by the characteristic lengths.
- `vacuumGaussian` : the anisotropic vacuum Gaussian, `exp(-∑ᵢ(xᵢ/ξᵢ)²/2)`.
- `loweringCLM_vacuumGaussian` : every `loweringCLM i` kills the vacuum Gaussian.
- `hasVacuum_vacuumGaussian` : `Q.vacuumGaussian` is a vacuum for `Q.toLadderSystem`.
- `loweringCLM_stdGaussian_of_xi_eq_one`, `hasVacuum_stdGaussian_of_forall_xi_eq_one` : the
    isotropic-unit-length special case.

## iii. Table of contents

- A. The standard Gaussian: derivative and momentum action
- B. The general, anisotropic vacuum
- C. The isotropic-unit-length special case

## iv. References

* None.
-/

@[expose] public section

namespace QuantumMechanics
namespace HarmonicOscillator
noncomputable section
open Complex Constants InnerProductSpace
open ContinuousLinearMap SchwartzMap

variable {d : ℕ} (Q : HarmonicOscillator d)

/-!

## A. The standard Gaussian: derivative and momentum action

`Q`-free prerequisites about the plain, unscaled Gaussian, reused by both the general anisotropic
case below and the isotropic-unit-length special case at the end of this file.

-/

/-- The real-valued Gaussian `exp(-‖x‖²/2)`'s coordinate derivative,
`∂ᵢ g = -xᵢ · g`. -/
lemma deriv_realGaussian (x : Space d) (i : Fin d) :
    Space.deriv i (fun x : Space d => Real.exp (-2⁻¹ * ‖x‖ ^ 2)) x =
      -x i * Real.exp (-2⁻¹ * ‖x‖ ^ 2) := by
  have hsq : DifferentiableAt ℝ (fun x : Space d => ‖x‖ ^ 2) x :=
    Space.norm_sq_differentiable.differentiableAt
  have hdiff2 : DifferentiableAt ℝ Real.exp (-2⁻¹ * ‖x‖ ^ 2) := Real.differentiableAt_exp
  have hdiff3 : DifferentiableAt ℝ (fun x : Space d => -2⁻¹ * ‖x‖ ^ 2) x := hsq.const_mul _
  change Space.deriv i (Real.exp ∘ (fun x : Space d => -2⁻¹ * ‖x‖ ^ 2)) x = _
  rw [Space.deriv_eq, fderiv_comp x hdiff2 hdiff3, fderiv_const_mul hsq (-2⁻¹ : ℝ),
    fderiv_norm_sq_apply]
  simp [Real.deriv_exp]

/-- `stdGaussian (Space d) ℂ`'s pointwise value is the real-valued Gaussian, cast to `ℂ`. -/
lemma stdGaussian_apply' (x : Space d) :
    (stdGaussian (Space d) ℂ : Space d → ℂ) x = Real.exp (-2⁻¹ * ‖x‖ ^ 2) := by
  simp [stdGaussian, gaussian₀, gaussian_apply]

/-- The coordinate derivative of the standard Gaussian, `∂ᵢ Ω = -xᵢ • Ω`. -/
lemma deriv_stdGaussian (x : Space d) (i : Fin d) :
    Space.deriv i (fun x : Space d => (stdGaussian (Space d) ℂ : Space d → ℂ) x) x =
      (-x i : ℂ) * (stdGaussian (Space d) ℂ : Space d → ℂ) x := by
  have hsq : DifferentiableAt ℝ (fun x : Space d => Real.exp (-2⁻¹ * ‖x‖ ^ 2)) x := by
    have hsq' : DifferentiableAt ℝ (fun x : Space d => ‖x‖ ^ 2) x :=
      Space.norm_sq_differentiable.differentiableAt
    exact Real.differentiableAt_exp.comp x (hsq'.const_mul (-2⁻¹ : ℝ))
  have heq : (fun x : Space d => (stdGaussian (Space d) ℂ : Space d → ℂ) x) =
      Complex.ofRealCLM ∘ (fun x : Space d => Real.exp (-2⁻¹ * ‖x‖ ^ 2)) := by
    funext x
    simp
  rw [heq, Space.deriv_eq, fderiv_comp x Complex.ofRealCLM.differentiableAt hsq]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.fderiv]
  rw [show (fderiv ℝ (fun x : Space d => Real.exp (-2⁻¹ * ‖x‖ ^ 2)) x) (Space.basis i) =
      Space.deriv i (fun x => Real.exp (-2⁻¹ * ‖x‖ ^ 2)) x from (Space.deriv_eq i _ x).symm,
    deriv_realGaussian, stdGaussian_apply', Complex.ofRealCLM_apply]
  push_cast
  ring

/-- The momentum operator applied to the standard Gaussian,
`𝐩ᵢ Ω = -iℏ·(-xᵢ)Ω = iℏxᵢ·Ω`. -/
lemma momentumCLM_stdGaussian (i : Fin d) (x : Space d) :
    (𝐩[d] i (stdGaussian (Space d) ℂ) : 𝓢(Space d, ℂ)) x =
      (I * ℏ * x i : ℂ) * (stdGaussian (Space d) ℂ : Space d → ℂ) x := by
  rw [momentumCLM_apply]
  show -I * ℏ * Space.deriv i (fun x => (stdGaussian (Space d) ℂ : Space d → ℂ) x) x = _
  rw [deriv_stdGaussian]
  ring

/-!

## B. The general, anisotropic vacuum

No isotropy assumption needed: every oscillator `Q` (any masses/frequencies, hence any
characteristic lengths `ξᵢ`) has an explicit vacuum, the Gaussian rescaled coordinatewise by `ξ`.

-/

/-- The diagonal rescaling of `Space d` by the characteristic lengths, `(Q.diagEquiv x) i = ξᵢxᵢ`.
Composing the standard Gaussian with its inverse turns the standard Gaussian's isotropic width into
the anisotropic width `ξᵢ` required by a vacuum of `Q`, whether or not `Q` itself is
isotropic (contrast `stdGaussian`/`hasVacuum_stdGaussian_of_forall_xi_eq_one` below, which only
covers `∀ i, ξᵢ = 1`). -/
noncomputable def diagEquiv (Q : HarmonicOscillator d) : Space d ≃L[ℝ] Space d :=
  (Space.equivPi d).trans <|
    (ContinuousLinearEquiv.piCongrRight
      fun i => ContinuousLinearEquiv.smulLeft (Units.mk0 (Q.ξ i) (Q.ξ_ne_zero i))).trans
      (Space.equivPi d).symm

@[simp] theorem diagEquiv_apply (x : Space d) (i : Fin d) : Q.diagEquiv x i = Q.ξ i * x i := rfl

@[simp] theorem diagEquiv_symm_apply (x : Space d) (i : Fin d) :
    Q.diagEquiv.symm x i = (Q.ξ i)⁻¹ * x i := rfl

/-- The vacuum Gaussian of `Q`: the anisotropic Gaussian `exp(-∑ᵢ(xᵢ/ξᵢ)²/2)`, `Q.diagEquiv`
applied to the standard one. Equals `stdGaussian (Space d) ℂ` exactly when every `ξᵢ = 1`. -/
noncomputable def vacuumGaussian (Q : HarmonicOscillator d) : 𝓢(Space d, ℂ) :=
  gaussian₀ ℂ Q.diagEquiv

lemma vacuumGaussian_apply (x : Space d) :
    (Q.vacuumGaussian : Space d → ℂ) x = Real.exp (-2⁻¹ * ‖Q.diagEquiv.symm x‖ ^ 2) := by
  simp [vacuumGaussian, gaussian₀, gaussian_apply]

/-- `Q.diagEquiv.symm` applied to a basis vector rescales it by `(ξᵢ)⁻¹`. -/
lemma diagEquiv_symm_basis (i : Fin d) :
    Q.diagEquiv.symm (Space.basis i) = (Q.ξ i)⁻¹ • Space.basis i := by
  ext j
  by_cases h : i = j <;> simp [diagEquiv_symm_apply, Space.basis_apply, h]

/-- The Fréchet derivative of the anisotropic Gaussian's real exponent `‖Q.diagEquiv.symm ·‖²`,
at the CLM level (mirrors `fderiv_norm_sq_apply`, composed with `Q.diagEquiv.symm`). -/
lemma fderiv_norm_sq_diagEquiv_symm (x : Space d) :
    fderiv ℝ (fun x : Space d => ‖Q.diagEquiv.symm x‖ ^ 2) x =
      (2 • innerSL ℝ (Q.diagEquiv.symm x)) ∘L (Q.diagEquiv.symm : Space d →L[ℝ] Space d) := by
  have hlin : DifferentiableAt ℝ Q.diagEquiv.symm x := Q.diagEquiv.symm.differentiableAt
  have hsq : DifferentiableAt ℝ (fun y : Space d => ‖y‖ ^ 2) (Q.diagEquiv.symm x) :=
    Space.norm_sq_differentiable.differentiableAt
  change fderiv ℝ ((fun y : Space d => ‖y‖ ^ 2) ∘ Q.diagEquiv.symm) x = _
  rw [fderiv_comp x hsq hlin, ContinuousLinearEquiv.fderiv, fderiv_norm_sq_apply]

/-- The real-valued anisotropic Gaussian's coordinate derivative,
`∂ᵢ g = -(xᵢ/ξᵢ²) · g`. -/
lemma deriv_realGaussian_diag (x : Space d) (i : Fin d) :
    Space.deriv i (fun x : Space d => Real.exp (-2⁻¹ * ‖Q.diagEquiv.symm x‖ ^ 2)) x =
      -(x i / (Q.ξ i) ^ 2) * Real.exp (-2⁻¹ * ‖Q.diagEquiv.symm x‖ ^ 2) := by
  have hsq : DifferentiableAt ℝ (fun x : Space d => ‖Q.diagEquiv.symm x‖ ^ 2) x :=
    (Space.norm_sq_differentiable.comp Q.diagEquiv.symm.differentiable).differentiableAt
  have hdiff2 : DifferentiableAt ℝ Real.exp (-2⁻¹ * ‖Q.diagEquiv.symm x‖ ^ 2) :=
    Real.differentiableAt_exp
  have hdiff3 : DifferentiableAt ℝ (fun x : Space d => -2⁻¹ * ‖Q.diagEquiv.symm x‖ ^ 2) x :=
    hsq.const_mul _
  change Space.deriv i (Real.exp ∘ (fun x : Space d => -2⁻¹ * ‖Q.diagEquiv.symm x‖ ^ 2)) x = _
  rw [Space.deriv_eq, fderiv_comp x hdiff2 hdiff3, fderiv_const_mul hsq (-2⁻¹ : ℝ),
    fderiv_norm_sq_diagEquiv_symm]
  simp [ContinuousLinearMap.comp_apply, smul_apply, ContinuousLinearEquiv.coe_coe,
    Q.diagEquiv_symm_basis i, Space.inner_basis, diagEquiv_symm_apply,
    innerSL_apply_apply, Real.deriv_exp]
  ring

/-- The coordinate derivative of the vacuum Gaussian, `∂ᵢ Ω = -(xᵢ/ξᵢ²) • Ω`. -/
lemma deriv_vacuumGaussian (x : Space d) (i : Fin d) :
    Space.deriv i (fun x : Space d => (Q.vacuumGaussian : Space d → ℂ) x) x =
      (-(x i / (Q.ξ i) ^ 2 : ℝ) : ℂ) * (Q.vacuumGaussian : Space d → ℂ) x := by
  have hsq : DifferentiableAt ℝ
      (fun x : Space d => Real.exp (-2⁻¹ * ‖Q.diagEquiv.symm x‖ ^ 2)) x := by
    have hsq' : DifferentiableAt ℝ (fun x : Space d => ‖Q.diagEquiv.symm x‖ ^ 2) x :=
      (Space.norm_sq_differentiable.comp Q.diagEquiv.symm.differentiable).differentiableAt
    exact Real.differentiableAt_exp.comp x (hsq'.const_mul (-2⁻¹ : ℝ))
  have heq : (fun x : Space d => (Q.vacuumGaussian : Space d → ℂ) x) =
      Complex.ofRealCLM ∘ (fun x : Space d => Real.exp (-2⁻¹ * ‖Q.diagEquiv.symm x‖ ^ 2)) := by
    funext x
    simp [Q.vacuumGaussian_apply]
  rw [heq, Space.deriv_eq, fderiv_comp x Complex.ofRealCLM.differentiableAt hsq]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.fderiv]
  rw [show (fderiv ℝ (fun x : Space d => Real.exp (-2⁻¹ * ‖Q.diagEquiv.symm x‖ ^ 2)) x)
      (Space.basis i) =
      Space.deriv i (fun x => Real.exp (-2⁻¹ * ‖Q.diagEquiv.symm x‖ ^ 2)) x
      from (Space.deriv_eq i _ x).symm,
    deriv_realGaussian_diag, Q.vacuumGaussian_apply, Complex.ofRealCLM_apply]
  push_cast
  ring

/-- The momentum operator applied to the vacuum Gaussian,
`𝐩ᵢ Ω = iℏ(xᵢ/ξᵢ²)·Ω`. -/
lemma momentumCLM_vacuumGaussian (i : Fin d) (x : Space d) :
    (𝐩[d] i (Q.vacuumGaussian) : 𝓢(Space d, ℂ)) x =
      (I * ℏ * (x i / (Q.ξ i) ^ 2 : ℝ) : ℂ) * (Q.vacuumGaussian : Space d → ℂ) x := by
  rw [momentumCLM_apply]
  show -I * ℏ * Space.deriv i (fun x => (Q.vacuumGaussian : Space d → ℂ) x) x = _
  rw [deriv_vacuumGaussian]
  ring

/-- Every `loweringCLM i` kills the vacuum Gaussian, without an isotropy or unit-length
assumption. -/
theorem loweringCLM_vacuumGaussian (i : Fin d) :
    Q.loweringCLM i (Q.vacuumGaussian) = 0 := by
  have hℏ : (ℏ : ℂ) ≠ 0 := by exact_mod_cast Constants.ℏ_ne_zero
  have hξ : (Q.ξ i : ℂ) ≠ 0 := by exact_mod_cast Q.ξ_ne_zero i
  ext x
  rw [loweringCLM_eq]
  simp only [smul_apply, add_apply, smul_eq_mul, zero_apply, positionCLM_apply]
  rw [show (𝐩 i) (Q.vacuumGaussian) x =
      (𝐩[d] i (Q.vacuumGaussian) : 𝓢(Space d, ℂ)) x from rfl,
    momentumCLM_vacuumGaussian]
  push_cast
  field_simp
  norm_num [Complex.I_sq]

/-- `Q.vacuumGaussian` is a vacuum for `Q.toLadderSystem`, without an isotropy assumption. -/
theorem hasVacuum_vacuumGaussian : Q.toLadderSystem.HasVacuum (Q.vacuumGaussian) where
  ne_zero := by
    intro h
    have hpt := congrFun (congrArg DFunLike.coe h) (⟨fun _ => 0⟩ : Space d)
    simp [Q.vacuumGaussian_apply] at hpt
  ann i := by
    show (Q.loweringCLM i).toLinearMap (Q.vacuumGaussian) = 0
    rw [show (Q.loweringCLM i).toLinearMap (Q.vacuumGaussian) =
        Q.loweringCLM i (Q.vacuumGaussian) from rfl,
      Q.loweringCLM_vacuumGaussian i]

/-!

## C. The isotropic-unit-length special case

-/

/-- Every `loweringCLM i` kills the standard Gaussian, provided that mode has unit
characteristic length. Independent of `hasVacuum_vacuumGaussian`/`loweringCLM_vacuumGaussian`
above: the hypothesis here is genuinely weaker (unit length in mode `i` alone, not every mode), so
this isn't a corollary of the general anisotropic result. -/
lemma loweringCLM_stdGaussian_of_xi_eq_one (i : Fin d) (hξ : Q.ξ i = 1) :
    Q.loweringCLM i (stdGaussian (Space d) ℂ) = 0 := by
  have hℏ : (ℏ : ℂ) ≠ 0 := by exact_mod_cast Constants.ℏ_ne_zero
  ext x
  rw [loweringCLM_eq]
  simp only [smul_apply, add_apply, smul_eq_mul, zero_apply, positionCLM_apply]
  rw [show (𝐩 i) (stdGaussian (Space d) ℂ) x =
      (𝐩[d] i (stdGaussian (Space d) ℂ) : 𝓢(Space d, ℂ)) x from rfl,
    momentumCLM_stdGaussian, hξ]
  field_simp
  norm_num [Complex.I_sq]

/-- `stdGaussian (Space d) ℂ` is a vacuum for `Q.toLadderSystem` when every mode has unit
characteristic length. -/
lemma hasVacuum_stdGaussian_of_forall_xi_eq_one (hξ : ∀ i, Q.ξ i = 1) :
    Q.toLadderSystem.HasVacuum (stdGaussian (Space d) ℂ) := by
  have heq : Q.vacuumGaussian = stdGaussian (Space d) ℂ := by
    ext x
    have hsymm : Q.diagEquiv.symm x = x := by
      ext j
      simp [diagEquiv_symm_apply, hξ j]
    rw [Q.vacuumGaussian_apply, stdGaussian_apply', hsymm]
  rw [← heq]
  exact Q.hasVacuum_vacuumGaussian

end
end HarmonicOscillator
end QuantumMechanics
