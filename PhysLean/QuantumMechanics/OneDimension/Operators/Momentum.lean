/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhysLean.QuantumMechanics.OneDimension.Operators.Unbounded
/-!

# Momentum operator

In this module we define:
- The momentum operator on functions `ℝ → ℂ`
- The momentum operator on Schwartz maps as an unbounded operator on the Hilbert space.

We show that plane waves are generalized eigenvectors of the momentum operator.

-/

@[expose] public section

namespace QuantumMechanics

namespace OneDimension
noncomputable section
open Constants
open HilbertSpace SchwartzMap

/-!

## The momentum operator on functions `ℝ → ℂ`

-/

/-- The momentum operator is defined as the map from `ℝ → ℂ` to `ℝ → ℂ` taking
  `ψ` to `- i ℏ ψ'`. -/
def momentumOperator (ψ : ℝ → ℂ) : ℝ → ℂ := fun x ↦ - Complex.I * ℏ * deriv ψ x

lemma momentumOperator_eq_smul (ψ : ℝ → ℂ) :
    momentumOperator ψ = fun x => (- Complex.I * ℏ) • deriv ψ x := by
  rfl

@[fun_prop]
lemma continuous_momentumOperator (ψ : ℝ → ℂ) (hψ : ContDiff ℝ 1 ψ) :
    Continuous (momentumOperator ψ) := by
  rw [momentumOperator_eq_smul]
  fun_prop

lemma momentumOperator_smul {ψ : ℝ → ℂ} (hψ : Differentiable ℝ ψ) (c : ℂ) :
    momentumOperator (c • ψ) = c • momentumOperator ψ := by
  rw [momentumOperator_eq_smul, momentumOperator_eq_smul]
  funext x
  simp only [neg_mul, Pi.smul_apply]
  rw [smul_comm]
  congr
  erw [deriv_smul]
  simp only [smul_eq_mul, deriv_const', zero_mul, add_zero]
  fun_prop
  fun_prop

lemma momentumOperator_add {ψ1 ψ2 : ℝ → ℂ}
    (hψ1 : Differentiable ℝ ψ1) (hψ2 : Differentiable ℝ ψ2) :
    momentumOperator (ψ1 + ψ2) = momentumOperator ψ1 + momentumOperator ψ2 := by
  rw [momentumOperator_eq_smul, momentumOperator_eq_smul, momentumOperator_eq_smul]
  funext x
  simp only [neg_mul, Pi.add_apply]
  rw [deriv_add (hψ1 x) (hψ2 x)]
  simp only [smul_eq_mul, neg_mul]
  ring

/-!

## The momentum operator on Schwartz maps

-/

/-- The parity operator on the Schwartz maps is defined as the linear map from
  `𝓢(ℝ, ℂ)` to itself, such that `ψ` is taken to `fun x => - I ℏ * ψ' x`. -/
def momentumOperatorSchwartz : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) where
  toFun ψ := (- Complex.I * ℏ) • SchwartzMap.derivCLM ℂ ℂ ψ
  map_add' ψ1 ψ2 := by
    simp only [neg_mul, map_add, smul_add, neg_smul]
  map_smul' a ψ := by
    simp only [neg_mul, map_smul, neg_smul, RingHom.id_apply]
    rw [smul_comm]
    simp
  cont := by fun_prop

lemma momentumOperatorSchwartz_apply (ψ : 𝓢(ℝ, ℂ))
    (x : ℝ) : (momentumOperatorSchwartz ψ) x = (- Complex.I * ℏ) * (deriv ψ x) := by
  rw [momentumOperatorSchwartz]
  rfl

/-- The unbounded momentum operator, whose domain is Schwartz maps. -/
def momentumOperatorUnbounded : UnboundedOperator schwartzIncl schwartzIncl_injective :=
  UnboundedOperator.ofSelfCLM momentumOperatorSchwartz

/-!

## Generalized eigenvectors of the momentum operator

-/

lemma planeWaveFunctional_generalized_eigenvector_momentumOperatorUnbounded (k : ℝ) :
    momentumOperatorUnbounded.IsGeneralizedEigenvector
      (planewaveFunctional k) (2 * Real.pi * ℏ * k) := by
  dsimp [momentumOperatorUnbounded]
  rw [UnboundedOperator.isGeneralizedEigenvector_ofSelfCLM_iff]
  intro ψ
  trans (-((Complex.I * ↑↑ℏ) •
      (SchwartzMap.fourierTransformCLM ℂ) ((SchwartzMap.derivCLM ℂ ℂ) ψ) k))
  · simp [momentumOperatorSchwartz]
    left
    rfl
  conv_lhs =>
    simp only [SchwartzMap.fourierTransformCLM_apply, smul_eq_mul]
  change -(Complex.I * ↑↑ℏ * (FourierTransform.fourier ((deriv ψ)) k)) = _
  rw [Real.fourier_deriv (SchwartzMap.integrable ψ)
      (SchwartzMap.differentiable (ψ)) (SchwartzMap.integrable ((SchwartzMap.derivCLM ℂ ℂ) ψ))]
  simp [planewaveFunctional]
  ring_nf
  simp only [Complex.I_sq, neg_mul, one_mul, neg_neg, mul_eq_mul_right_iff, mul_eq_mul_left_iff,
    mul_eq_zero, Complex.ofReal_eq_zero, Real.pi_ne_zero, or_false, OfNat.ofNat_ne_zero]
  left
  rfl

/-!

## The momentum operator is self adjoint

-/

lemma momentumOperatorUnbounded_isSelfAdjoint : momentumOperatorUnbounded.IsSelfAdjoint := by
  intro ψ1 ψ2
  dsimp [momentumOperatorUnbounded]
  rw [schwartzIncl_inner, schwartzIncl_inner]
  conv_rhs =>
    change ∫ (x : ℝ), (starRingEnd ℂ) ((ψ1) x) *
      ((-Complex.I * ↑↑ℏ) * (SchwartzMap.derivCLM ℂ ℂ) (ψ2) x)
    enter [2, x]
    rw [← mul_assoc]
    rw [mul_comm _ (-Complex.I * ↑↑ℏ)]
    rw [mul_assoc]
    simp only [SchwartzMap.derivCLM_apply]
    rw [← fderiv_apply_one_eq_deriv]
  rw [MeasureTheory.integral_const_mul]
  rw [integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable]
  conv_rhs =>
    rw [← MeasureTheory.integral_neg, ← MeasureTheory.integral_const_mul]
  congr
  funext x
  conv_rhs =>
    enter [2, 1, 1]
    change (fderiv ℝ (fun a => star ((ψ1) a)) x) 1
    rw [fderiv_star]
  simp [momentumOperatorSchwartz_apply]
  ring
  · apply MeasureTheory.Integrable.mul_of_top_left
    · conv =>
        enter [1, x]
        change (fderiv ℝ (fun a => star ((ψ1) a)) x) 1
        rw [fderiv_star]
        change (starL' ℝ) (SchwartzMap.derivCLM ℂ ℂ (ψ1) x)
      rw [ContinuousLinearEquiv.integrable_comp_iff]
      exact SchwartzMap.integrable ((SchwartzMap.derivCLM ℂ ℂ) (ψ1))
    · exact SchwartzMap.memLp_top (ψ2) MeasureTheory.volume
  · apply MeasureTheory.Integrable.mul_of_top_left
    · change MeasureTheory.Integrable
        (fun x => (starL' ℝ : ℂ ≃L[ℝ] ℂ) ((ψ1) x)) MeasureTheory.volume
      rw [ContinuousLinearEquiv.integrable_comp_iff]
      exact SchwartzMap.integrable (ψ1)
    · change MeasureTheory.MemLp
        (fun x => SchwartzMap.derivCLM ℂ ℂ (ψ2) x) ⊤ MeasureTheory.volume
      exact SchwartzMap.memLp_top ((SchwartzMap.derivCLM ℂ ℂ) (ψ2))
          MeasureTheory.volume
  · apply MeasureTheory.Integrable.mul_of_top_left
    · change MeasureTheory.Integrable
        (fun x => (starL' ℝ : ℂ ≃L[ℝ] ℂ) ((ψ1) x)) MeasureTheory.volume
      rw [ContinuousLinearEquiv.integrable_comp_iff]
      exact SchwartzMap.integrable (ψ1)
    · exact SchwartzMap.memLp_top (ψ2) MeasureTheory.volume
  · apply Differentiable.star
    exact SchwartzMap.differentiable (ψ1)
  · exact SchwartzMap.differentiable (ψ2)

end
end OneDimension
end QuantumMechanics
