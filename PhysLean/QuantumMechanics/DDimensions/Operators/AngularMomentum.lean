/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
import PhysLean.QuantumMechanics.DDimensions.Operators.Position
import PhysLean.QuantumMechanics.DDimensions.Operators.Momentum
/-!

# Angular momentum operator

## i. Overview

In this module we introduce several angular momentum operators for quantum mechanics on `Space d`.

## ii. Key results

Definitions:
- `angularMomentumOperator` : (components of) the angular momentum operator acting on Schwartz maps
    `𝓢(Space d, ℂ)` as `𝐱ᵢ∘𝐩ⱼ - 𝐱ⱼ∘𝐩ᵢ`.
- `angularMomentumOperatorSqr` : the operator acting on Schwartz maps `𝓢(Space d, ℂ)`
    as `½ ∑ᵢⱼ 𝐋ᵢⱼ∘𝐋ᵢⱼ`.
- `angularMomentumOperator2D` : the (pseudo)scalar angular momentum operator for `d = 2`.
- `angularMomentumOperator3D` : the (pseudo)vector angular momentum operator for `d = 3`.

Notation:
- `𝐋[i,j]` for `angularMomentumOperator i j`
- `𝐋²` for `angularMomentumOperatorSqr`

## iii. Table of contents

- A. Angular momentum operator
  - A.1 Antisymmetry
- B. Angular momentum squared operator
- C. Special cases in low dimensions

## iv. References

-/

namespace QuantumMechanics
noncomputable section
open Constants
open ContDiff SchwartzMap

/-!

## A. Angular momentum operator

-/

/-- Component `i j` of the angular momentum operator is the continuous linear map
from `𝓢(Space d, ℂ)` to itself defined by `𝐋ᵢⱼ ≔ 𝐱ᵢ∘𝐩ⱼ - 𝐱ⱼ∘𝐩ᵢ`. -/
def angularMomentumOperator {d : ℕ} (i j : Fin d) : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ) :=
  𝐱[i] ∘L 𝐩[j] - 𝐱[j] ∘L 𝐩[i]

@[inherit_doc angularMomentumOperator]
notation "𝐋[" i "," j "]" => angularMomentumOperator i j

lemma angularMomentumOperator_apply_fun {d : ℕ} (i j : Fin d) (ψ : 𝓢(Space d, ℂ)) :
    𝐋[i,j] ψ = 𝐱[i] (𝐩[j] ψ) - 𝐱[j] (𝐩[i] ψ) := rfl

lemma angularMomentumOperator_apply {d : ℕ} (i j : Fin d) (ψ : 𝓢(Space d, ℂ)) (x : Space d) :
    𝐋[i,j] ψ x = 𝐱[i] (𝐩[j] ψ) x - 𝐱[j] (𝐩[i] ψ) x := rfl

/-!

### A.1 Antisymmetry

-/

/-- The angular momentum operator is antisymmetric, `𝐋ᵢⱼ = -𝐋ⱼᵢ` -/
lemma angularMomentumOperator_antisymm {d : ℕ} (i j : Fin d) : 𝐋[i,j] = - 𝐋[j,i] :=
  Eq.symm (neg_sub _ _)

/-- Angular momentum operator components with repeated index vanish, `𝐋ᵢᵢ = 0`. -/
lemma angularMomentumOperator_eq_zero {d : ℕ} (i : Fin d) : 𝐋[i,i] = 0 := sub_self _

/-!

## B. Angular momentum squared operator

-/

/-- The square of the angular momentum operator, `𝐋² ≔ ½ ∑ᵢⱼ 𝐋ᵢⱼ∘𝐋ᵢⱼ`. -/
def angularMomentumOperatorSqr {d : ℕ} : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ) :=
  (2 : ℂ)⁻¹ • ∑ i, ∑ j, 𝐋[i,j] ∘L 𝐋[i,j]

@[inherit_doc angularMomentumOperatorSqr]
notation "𝐋²" => angularMomentumOperatorSqr

lemma angularMomentumOperatorSqr_apply_fun {d : ℕ} (ψ : 𝓢(Space d, ℂ)) :
    𝐋² ψ = (2 : ℂ)⁻¹ • ∑ i, ∑ j, 𝐋[i,j] (𝐋[i,j] ψ) := by
  dsimp only [angularMomentumOperatorSqr]
  simp only [ContinuousLinearMap.coe_sum', ContinuousLinearMap.coe_smul',
    ContinuousLinearMap.coe_comp', Finset.sum_apply, Pi.smul_apply, Function.comp_apply]

lemma angularMomentumOperatorSqr_apply {d : ℕ} (ψ : 𝓢(Space d, ℂ)) (x : Space d) :
    𝐋² ψ x = (2 : ℂ)⁻¹ * ∑ i, ∑ j, 𝐋[i,j] (𝐋[i,j] ψ) x := by
  rw [angularMomentumOperatorSqr_apply_fun]
  simp only [smul_apply, sum_apply, smul_eq_mul]

/-!

## C. Special cases in low dimensions

  • d = 1 : The angular momentum operator is trivial.

  • d = 2 : The angular momentum operator has only one independent component, 𝐋₀₁, which may
            be thought of as a (pseudo)scalar operator.

  • d = 3 : The angular momentum operator has three independent components, 𝐋₀₁, 𝐋₁₂ and 𝐋₂₀.
            Dualizing using the Levi-Civita symbol produces the familiar (pseudo)vector angular
            momentum operator with components 𝐋₀ = 𝐋₁₂, 𝐋₁ = 𝐋₂₀ and 𝐋₂ = 𝐋₀₁.

-/

/-- In one dimension the angular momentum operator is trivial. -/
lemma angularMomentumOperator1D_trivial (i j : Fin 1) : 𝐋[i,j] = 0 := by
  fin_cases i, j
  exact angularMomentumOperator_eq_zero 0

/-- The angular momentum (pseudo)scalar operator in two dimensions, `𝐋 ≔ 𝐋₀₁`. -/
def angularMomentumOperator2D : 𝓢(Space 2, ℂ) →L[ℂ] 𝓢(Space 2, ℂ) := 𝐋[0,1]

/-- The angular momentum (pseudo)vector operator in three dimension, `𝐋ᵢ ≔ ½ ∑ⱼₖ εᵢⱼₖ 𝐋ⱼₖ`. -/
def angularMomentumOperator3D (i : Fin 3) : 𝓢(Space 3, ℂ) →L[ℂ] 𝓢(Space 3, ℂ) :=
  match i with
    | 0 => 𝐋[1,2]
    | 1 => 𝐋[2,0]
    | 2 => 𝐋[0,1]

end
end QuantumMechanics
