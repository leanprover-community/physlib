/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Star
public import Physlib.QuantumMechanics.Operators.OneDimension.Unbounded
public import Physlib.QuantumMechanics.HilbertSpaces.OneDimension.SchwartzSubmodule
public import Physlib.QuantumMechanics.PlanckConstant
public import Physlib.QuantumMechanics.HilbertSpaces.OneDimension.PlaneWaves
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
open _root_.QuantumMechanics.OneDimension.HilbertSpace
open SchwartzMap

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
  simp only [Pi.smul_apply, deriv_const_smul _ (hψ x), smul_comm (-Complex.I * ℏ) c]

lemma momentumOperator_add {ψ1 ψ2 : ℝ → ℂ}
    (hψ1 : Differentiable ℝ ψ1) (hψ2 : Differentiable ℝ ψ2) :
    momentumOperator (ψ1 + ψ2) = momentumOperator ψ1 + momentumOperator ψ2 := by
  rw [momentumOperator_eq_smul, momentumOperator_eq_smul, momentumOperator_eq_smul]
  funext x
  simp only [Pi.add_apply, deriv_add (hψ1 x) (hψ2 x), smul_eq_mul]
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
    simp only [map_smul, RingHom.id_apply, smul_comm (-Complex.I * ℏ) a]
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
  · simp [momentumOperatorSchwartz, planewaveFunctional_apply,
      SchwartzMap.fourierTransformCLM_apply]
  simp only [SchwartzMap.fourierTransformCLM_apply, smul_eq_mul]
  change -(Complex.I * ↑↑ℏ * (FourierTransform.fourier ((deriv ψ)) k)) = _
  rw [Real.fourier_deriv (SchwartzMap.integrable ψ)
      (SchwartzMap.differentiable (ψ)) (SchwartzMap.integrable ((SchwartzMap.derivCLM ℂ ℂ) ψ))]
  simp only [planewaveFunctional_apply, smul_eq_mul]
  ring_nf
  simp [Complex.I_sq]
  exact Or.inl rfl

/-!

## The momentum operator is symmetric

-/

lemma momentumOperatorUnbounded_isSymmetric : momentumOperatorUnbounded.IsSymmetric := by
  intro ψ1 ψ2
  have hint : ∀ f g : 𝓢(ℝ, ℂ),
      MeasureTheory.Integrable (fun x => star (f x) * g x) MeasureTheory.volume :=
    fun f g => ((ContinuousLinearEquiv.integrable_comp_iff (starL' ℝ)).mpr
      (SchwartzMap.integrable f)).mul_of_top_left (SchwartzMap.memLp_top g)
  dsimp [momentumOperatorUnbounded]
  rw [schwartzIncl_inner, schwartzIncl_inner]
  conv_rhs =>
    enter [2, x]
    rw [momentumOperatorSchwartz_apply, ← fderiv_apply_one_eq_deriv, ← mul_assoc,
      mul_comm _ (-Complex.I * ↑↑ℏ), mul_assoc]
  rw [MeasureTheory.integral_const_mul, integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable,
    ← MeasureTheory.integral_neg, ← MeasureTheory.integral_const_mul]
  · simp only [starRingEnd_apply, fderiv_star]
    simp [momentumOperatorSchwartz_apply, mul_assoc]
  · simp only [starRingEnd_apply, fderiv_star]
    exact hint (SchwartzMap.derivCLM ℂ ℂ ψ1) ψ2
  · exact hint ψ1 (SchwartzMap.derivCLM ℂ ℂ ψ2)
  · exact hint ψ1 ψ2
  · exact fun x _ => (SchwartzMap.differentiable ψ1).star x
  · fun_prop

end
end OneDimension
end QuantumMechanics
