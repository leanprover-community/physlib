/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhysLean.QuantumMechanics.OneDimension.HilbertSpace.PositionStates
public import PhysLean.QuantumMechanics.OneDimension.Operators.Unbounded
public import PhysLean.Mathematics.Distribution.PowMul
/-!

# Position operator

In this module we define:
- The position operator on functions `ℝ → ℂ`
- The position operator on Schwartz maps as an unbounded operator on the Hilbert space.

We show that position wavefunctions are generalized eigenvectors of the position operator.

-/

@[expose] public section

namespace QuantumMechanics

namespace OneDimension
noncomputable section
open Constants
open HilbertSpace

/-!

## The position operator on functions `ℝ → ℂ`

-/

/-- The position operator is defined as the linear map from `ℝ → ℂ` to `ℝ → ℂ` taking
  `ψ` to `x * ψ`. -/
def positionOperator : (ℝ → ℂ) →ₗ[ℂ] ℝ → ℂ where
  toFun ψ := fun x ↦ x * ψ x
  map_add' ψ1 ψ2 := by
    funext x
    simp only [Pi.add_apply]
    ring
  map_smul' a ψ1 := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring
/-!

## The position operator on Schwartz maps

-/

open ContDiff

open SchwartzMap

/-- The parity operator on the Schwartz maps is defined as the linear map from
  `𝓢(ℝ, ℂ)` to itself, such that `ψ` is taken to `fun x => x * ψ x`. -/
def positionOperatorSchwartz : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) := Distribution.powOneMul ℂ

lemma positionOperatorSchwartz_apply_fun (ψ : 𝓢(ℝ, ℂ)) :
    (positionOperatorSchwartz ψ) = fun x => x * ψ x := by
  simp [positionOperatorSchwartz]
  rfl

@[simp]
lemma positionOperatorSchwartz_apply (ψ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    (positionOperatorSchwartz ψ) x = x * ψ x := by
  simp [positionOperatorSchwartz]
  rfl

/-- The unbounded position operator, whose domain is Schwartz maps. -/
def positionOperatorUnbounded : UnboundedOperator schwartzIncl schwartzIncl_injective :=
  UnboundedOperator.ofSelfCLM positionOperatorSchwartz

/-!

## Generalized eigenvectors of the momentum operator

-/

lemma positionStates_generalized_eigenvector_positionOperatorUnbounded (x : ℝ) :
    positionOperatorUnbounded.IsGeneralizedEigenvector (positionState x) x := by
  dsimp [positionOperatorUnbounded]
  rw [UnboundedOperator.isGeneralizedEigenvector_ofSelfCLM_iff]
  intro ψ
  simp [positionState_apply]

/-!

## Position operator is self adjoint

-/

lemma positionOperatorUnbounded_isSelfAdjoint :
    positionOperatorUnbounded.IsSelfAdjoint := by
  intro ψ1 ψ2
  dsimp [positionOperatorUnbounded]
  rw [schwartzIncl_inner, schwartzIncl_inner]
  congr
  funext x
  simp only [positionOperatorSchwartz_apply, map_mul, Complex.conj_ofReal]
  ring

end
end OneDimension
end QuantumMechanics
