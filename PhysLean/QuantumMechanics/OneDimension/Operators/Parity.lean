/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhysLean.QuantumMechanics.OneDimension.HilbertSpace.PositionStates
public import PhysLean.QuantumMechanics.OneDimension.Operators.Unbounded
/-!

# Parity operator

-/

@[expose] public section

namespace QuantumMechanics

namespace OneDimension
noncomputable section

namespace HilbertSpace
open MeasureTheory SchwartzMap

/-!

## The parity operator on functions

-/

/-- The parity operator is defined as linear map from `ℝ → ℂ` to itself, such that
  `ψ` is taken to `fun x => ψ (-x)`. -/
def parityOperator : (ℝ → ℂ) →ₗ[ℂ] (ℝ → ℂ) where
  toFun ψ := fun x => ψ (-x)
  map_add' ψ1 ψ2 := by
    funext x
    simp
  map_smul' a ψ1 := by
    funext x
    simp

/-!

## The parity operator on Schwartz maps

-/

/-- The parity operator on the Schwartz maps is defined as the linear map from
  `𝓢(ℝ, ℂ)` to itself, such that `ψ` is taken to `fun x => ψ (-x)`. -/
def parityOperatorSchwartz : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) := by
  refine (SchwartzMap.compCLM ℂ (g := (fun x => - x : ℝ → ℝ)) ⟨?_, ?_⟩ ?_)
  · fun_prop
  · intro n
    simp only [Real.norm_eq_abs]
    use 1, 1
    intro x
    simp only [pow_one, one_mul]
    erw [iteratedFDeriv_neg_apply]
    simp only [norm_neg]
    match n with
    | 0 => simp
    | 1 =>
      rw [iteratedFDeriv_succ_eq_comp_right]
      simp [ContinuousLinearMap.norm_id]
    | .succ (.succ n) =>
      rw [iteratedFDeriv_succ_eq_comp_right]
      simp only [Nat.succ_eq_add_one, fderiv_id', Function.comp_apply,
        LinearIsometryEquiv.norm_map, ge_iff_le]
      rw [iteratedFDeriv_const_of_ne]
      simp only [Pi.zero_apply, norm_zero]
      apply add_nonneg
      · exact zero_le_one' ℝ
      · exact abs_nonneg x
      simp
  · simp
    use 1, 1
    intro x
    simp

/-- The unbounded parity operator, whose domain is Schwartz maps. -/
def parityOperatorUnbounded : UnboundedOperator schwartzIncl schwartzIncl_injective :=
  UnboundedOperator.ofSelfCLM parityOperatorSchwartz

@[simp]
lemma parityOperatorSchwartz_parityOperatorSchwartz (ψ : 𝓢(ℝ, ℂ)) :
    parityOperatorSchwartz (parityOperatorSchwartz ψ) = ψ := by
  ext x
  simp [parityOperatorSchwartz]

/-!

## Parity operator is self adjoint

-/

open InnerProductSpace

lemma parityOperatorUnbounded_isSelfAdjoint :
    parityOperatorUnbounded.IsSelfAdjoint := by
  intro ψ1 ψ2
  dsimp [parityOperatorUnbounded]
  rw [schwartzIncl_inner, schwartzIncl_inner]
  let f (x : ℝ) :=
    (starRingEnd ℂ) ((ψ1) (-x)) * (ψ2) x
  change ∫ (x : ℝ), f x = _
  trans ∫ (x : ℝ), f (- x)
  · exact Eq.symm (integral_neg_eq_self f volume)
  · simp only [neg_neg, f]
    rfl

open InnerProductSpace

end HilbertSpace
end
end OneDimension
end QuantumMechanics
