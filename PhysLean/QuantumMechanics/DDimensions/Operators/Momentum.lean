/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
import PhysLean.QuantumMechanics.DDimensions.Operators.Unbounded
import PhysLean.QuantumMechanics.DDimensions.SpaceDHilbertSpace.SchwartzSubmodule
import PhysLean.QuantumMechanics.PlanckConstant
import PhysLean.SpaceAndTime.Space.Derivatives.Basic
/-!

# Momentum operators

## i. Overview

In this module we introduce several momentum operators for quantum mechanics on `Space d`.

## ii. Key results

Definitions:
- `momentumOperator` : (components of) the momentum vector operator acting on Schwartz maps
    `𝓢(Space d, ℂ)` as `-iℏ∂ᵢ`.
- `momentumOperatorSqr` : operator acting on Schwartz maps `𝓢(Space d, ℂ)` as `∑ᵢ 𝐩[i]∘𝐩[i]`.
- `momentumUnboundedOperator` : a symmetric unbounded operator acting on the Schwartz submodule
    of the Hilbert space `SpaceDHilbertSpace d`.

Notation:
- `𝐩[i]` for `momentumOperator i`
- `𝐩²` for `momentumOperatorSqr`

## iii. Table of contents

- A. Momentum vector operator
- B. Momentum-squared operator
- C. Unbounded momentum vector operator

## iv. References

-/

namespace QuantumMechanics
noncomputable section
open Constants
open Space
open ContDiff SchwartzMap

variable {d : ℕ} (i : Fin d)

/-!

## A. Momentum vector operator

-/

/-- Component `i` of the momentum operator is the continuous linear map
from `𝓢(Space d, ℂ)` to itself which maps `ψ` to `-iℏ ∂ᵢψ`. -/
def momentumOperator : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ) :=
  (- Complex.I * ℏ) • (SchwartzMap.evalCLM ℂ (Space d) ℂ (basis i)) ∘L
    (SchwartzMap.fderivCLM ℂ (Space d) ℂ)

@[inherit_doc momentumOperator]
notation "𝐩[" i "]" => momentumOperator i

lemma momentumOperator_apply_fun (ψ : 𝓢(Space d, ℂ)) :
    𝐩[i] ψ = (- Complex.I * ℏ) • ∂[i] ψ := rfl

@[simp]
lemma momentumOperator_apply (ψ : 𝓢(Space d, ℂ)) (x : Space d) :
    𝐩[i] ψ x = - Complex.I * ℏ * ∂[i] ψ x := rfl

/-!

## B. Momentum-squared operator

-/

/-- The square of the momentum operator, `𝐩² ≔ ∑ᵢ 𝐩ᵢ∘𝐩ᵢ`. -/
def momentumOperatorSqr : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ) := ∑ i, 𝐩[i] ∘L 𝐩[i]

@[inherit_doc momentumOperatorSqr]
notation "𝐩²" => momentumOperatorSqr

lemma momentumOperatorSqr_apply (ψ : 𝓢(Space d, ℂ)) (x : Space d) :
    𝐩² ψ x = ∑ i, 𝐩[i] (𝐩[i] ψ) x := by
  dsimp only [momentumOperatorSqr]
  rw [← SchwartzMap.coe_coeHom]
  simp only [ContinuousLinearMap.coe_sum', ContinuousLinearMap.coe_comp', Finset.sum_apply,
    Function.comp_apply, map_sum]

/-!

## C. Unbounded momentum vector operator

-/

open SpaceDHilbertSpace

/-- The momentum operators defined on the Schwartz submodule. -/
def momentumOperatorSchwartz : schwartzSubmodule d →ₗ[ℂ] schwartzSubmodule d :=
  schwartzEquiv.toLinearMap ∘ₗ 𝐩[i].toLinearMap ∘ₗ schwartzEquiv.symm.toLinearMap

@[sorryful]
lemma momentumOperatorSchwartz_isSymmetric : (momentumOperatorSchwartz i).IsSymmetric := by
  intro ψ ψ'
  obtain ⟨f, rfl⟩ := schwartzEquiv.surjective ψ
  obtain ⟨f', rfl⟩ := schwartzEquiv.surjective ψ'
  unfold momentumOperatorSchwartz
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, ContinuousLinearMap.coe_coe,
    Function.comp_apply, LinearEquiv.symm_apply_apply, schwartzEquiv_inner, momentumOperator_apply,
    neg_mul, map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal, neg_neg, mul_neg]
  -- Need integration by parts and `starRingEnd ∂[i] = ∂[i] starRingEnd`:
  -- ⊢ ∫ (x : Space d), Complex.I * ↑↑ℏ * (starRingEnd ℂ) (Space.deriv i (⇑f) x) * f' x =
  -- ∫ (x : Space d), -((starRingEnd ℂ) (f x) * (Complex.I * ↑↑ℏ * Space.deriv i (⇑f') x))
  sorry

/-- The symmetric momentum unbounded operators with domain the Schwartz submodule
  of the Hilbert space. -/
@[sorryful]
def momentumUnboundedOperator : UnboundedOperator (SpaceDHilbertSpace d) (SpaceDHilbertSpace d) :=
  UnboundedOperator.ofSymmetric (schwartzSubmodule_dense d) (momentumOperatorSchwartz i)
    (momentumOperatorSchwartz_isSymmetric i)

end
end QuantumMechanics
