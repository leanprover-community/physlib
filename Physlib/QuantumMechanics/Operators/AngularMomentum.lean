/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Physlib.QuantumMechanics.Operators.Commutation
/-!

# Angular momentum operator

## i. Overview

In this module we introduce several angular momentum operators for quantum mechanics on `Space d`.
Each component also acts symmetrically on `SpaceDHilbertSpace d` with domain `SchwartzSubmodule d`.
We prove its symmetry and commutation relations.

## ii. Key results

Definitions:
- `angularMomentumCLM` : (components of) the angular momentum operator acting on Schwartz maps
    `𝓢(Space d, ℂ)` as `𝐱ᵢ∘𝐩ⱼ - 𝐱ⱼ∘𝐩ᵢ`.
- `angularMomentumOperatorSqr` : the operator acting on Schwartz maps `𝓢(Space d, ℂ)`
    as `½ ∑ᵢⱼ 𝐋ᵢⱼ∘𝐋ᵢⱼ`.
- `angularMomentumOperator2D` : the (pseudo)scalar angular momentum operator for `d = 2`.
- `angularMomentumOperator3D` : the (pseudo)vector angular momentum operator for `d = 3`.
- `angularMomentumOperator` : each component as a partially defined operator on
    `SpaceDHilbertSpace d`, preserving the dense Schwartz submodule.

Lemmas:
- `angularMomentumOperator_isSymmetric` : angular momentum is symmetric on the Schwartz domain.
- `angularMomentum_commutation_angularMomentum` : angular momenta generate an `𝔰𝔬(d)` algebra.

Notation:
- `𝐋` for `angularMomentumCLM`
- `𝐋²` for `angularMomentumOperatorSqr`

## iii. Table of contents

- A. Angular momentum operator
  - A.1 Antisymmetry
- B. Angular momentum squared operator
- C. Special cases in low dimensions
- D. Hilbert-space angular momentum operator
- E. Commutation relations
  - E.1. Angular momentum / position
  - E.2. Angular momentum / momentum
  - E.3. Angular momentum / angular momentum

## iv. References

* None.
-/

@[expose] public section

namespace QuantumMechanics
noncomputable section
open Constants
open ContDiff SchwartzMap

/-!

## A. Angular momentum operator

-/

/-- Component `i j` of the angular momentum operator is the continuous linear map
from `𝓢(Space d, ℂ)` to itself defined by `𝐋ᵢⱼ ≔ 𝐱ᵢ∘𝐩ⱼ - 𝐱ⱼ∘𝐩ᵢ`. -/
def angularMomentumCLM {d : ℕ} (i j : Fin d) : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ) :=
  𝐱 i ∘L 𝐩 j - 𝐱 j ∘L 𝐩 i

@[inherit_doc angularMomentumCLM]
notation "𝐋" => angularMomentumCLM

@[inherit_doc angularMomentumCLM]
notation "𝐋[" d' "]" => angularMomentumCLM (d := d')

lemma angularMomentumCLM_apply_fun {d : ℕ} (i j : Fin d) (ψ : 𝓢(Space d, ℂ)) :
    𝐋 i j ψ = 𝐱 i (𝐩 j ψ) - 𝐱 j (𝐩 i ψ) := rfl

lemma angularMomentumCLM_apply {d : ℕ} (i j : Fin d) (ψ : 𝓢(Space d, ℂ)) (x : Space d) :
    𝐋 i j ψ x = 𝐱 i (𝐩 j ψ) x - 𝐱 j (𝐩 i ψ) x := rfl

/-!

### A.1 Antisymmetry

-/

/-- The angular momentum operator is antisymmetric, `𝐋ᵢⱼ = -𝐋ⱼᵢ` -/
lemma angularMomentumCLM_antisymm {d : ℕ} (i j : Fin d) : 𝐋 i j = -𝐋 j i :=
  Eq.symm (neg_sub _ _)

/-- Angular momentum operator components with repeated index vanish, `𝐋ᵢᵢ = 0`. -/
lemma angularMomentumCLM_eq_zero {d : ℕ} (i : Fin d) : 𝐋 i i = 0 := sub_self _

/-!

## B. Angular momentum squared operator

-/

/-- The square of the angular momentum operator, `𝐋² ≔ ½ ∑ᵢⱼ 𝐋ᵢⱼ∘𝐋ᵢⱼ`. -/
def angularMomentumOperatorSqr {d : ℕ} : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ) :=
  (2 : ℂ)⁻¹ • ∑ i, ∑ j, 𝐋 i j ∘L 𝐋 i j

@[inherit_doc angularMomentumOperatorSqr]
notation "𝐋²" => angularMomentumOperatorSqr

@[inherit_doc angularMomentumOperatorSqr]
notation "𝐋²[" d' "]" => angularMomentumOperatorSqr (d := d')

lemma angularMomentumOperatorSqr_apply_fun {d : ℕ} (ψ : 𝓢(Space d, ℂ)) :
    𝐋² ψ = (2 : ℂ)⁻¹ • ∑ i, ∑ j, 𝐋 i j (𝐋 i j ψ) := by
  simp only [angularMomentumOperatorSqr, FunLike.coe_sum, FunLike.coe_smul,
    ContinuousLinearMap.coe_comp, Finset.sum_apply, Pi.smul_apply, Function.comp_apply]

lemma angularMomentumOperatorSqr_apply {d : ℕ} (ψ : 𝓢(Space d, ℂ)) (x : Space d) :
    𝐋² ψ x = (2 : ℂ)⁻¹ * ∑ i, ∑ j, 𝐋 i j (𝐋 i j ψ) x := by
  simp only [angularMomentumOperatorSqr_apply_fun, smul_apply, sum_apply, smul_eq_mul]

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
lemma angularMomentumOperator1D_trivial : 𝐋[1] = 0 := by
  ext i j
  simp [Subsingleton.elim i j, angularMomentumCLM_eq_zero]

/-- The angular momentum (pseudo)scalar operator in two dimensions, `𝐋 ≔ 𝐋₀₁`. -/
def angularMomentumOperator2D : 𝓢(Space 2, ℂ) →L[ℂ] 𝓢(Space 2, ℂ) := 𝐋 0 1

/-- The angular momentum (pseudo)vector operator in three dimension, `𝐋ᵢ ≔ ½ ∑ⱼₖ εᵢⱼₖ 𝐋ⱼₖ`. -/
def angularMomentumOperator3D (i : Fin 3) : 𝓢(Space 3, ℂ) →L[ℂ] 𝓢(Space 3, ℂ) :=
  match i with
    | 0 => 𝐋 1 2
    | 1 => 𝐋 2 0
    | 2 => 𝐋 0 1

/-!
## D. Hilbert-space angular momentum operator
-/

open MeasureTheory SpaceDHilbertSpace SchwartzSubmodule

variable {d : ℕ} (i j : Fin d)

/-- Component `i j` of angular momentum on the Hilbert space, with Schwartz domain.
This transports the existing Schwartz-space operator `𝐋 i j`. -/
def angularMomentumOperator : SpaceDHilbertSpace d →ₗ.[ℂ] SpaceDHilbertSpace d where
  domain := SchwartzSubmodule d
  toFun := (schwartzIncl volume).1 ∘ₗ (𝐋 i j).1 ∘ₗ (schwartzEquiv volume).symm.1

lemma angularMomentumOperator_domain_eq :
    (angularMomentumOperator i j).domain = SchwartzSubmodule d := rfl

lemma angularMomentumOperator_apply (ψ : SchwartzSubmodule d) :
    angularMomentumOperator i j ψ =
      schwartzEquiv volume (𝐋 i j ((schwartzEquiv volume).symm ψ)) := rfl

lemma angularMomentumOperator_apply_ae (ψ : SchwartzSubmodule d) :
    angularMomentumOperator i j ψ =ᵐ[volume] 𝐋 i j ((schwartzEquiv volume).symm ψ) :=
  schwartzEquiv_coe_ae _

lemma angularMomentumOperator_range (ψ : SchwartzSubmodule d) :
    angularMomentumOperator i j ψ ∈ SchwartzSubmodule d := by
  simp [angularMomentumOperator_apply]

lemma angularMomentumOperator_hasDenseDomain :
    (angularMomentumOperator i j).HasDenseDomain := SchwartzSubmodule.dense d _

/-- Reversing the order of position and momentum leaves angular momentum unchanged. -/
lemma angularMomentumCLM_eq_momentum_position :
    𝐋 i j = 𝐩 j ∘L 𝐱 i - 𝐩 i ∘L 𝐱 j := by
  rw [momentum_comp_position_eq, momentum_comp_position_eq, KroneckerDelta.symm j i]
  simp [angularMomentumCLM]

/-- Each angular momentum component is symmetric on the Schwartz domain. -/
lemma angularMomentumOperator_isSymmetric :
    (angularMomentumOperator i j).IsSymmetric := by
  intro ψ φ
  obtain ⟨f, rfl⟩ := (schwartzEquiv volume).surjective ψ
  obtain ⟨g, rfl⟩ := (schwartzEquiv volume).surjective φ
  simp only [angularMomentumOperator_apply, LinearEquiv.symm_apply_apply]
  rw [angularMomentumCLM_apply_fun, map_sub, Submodule.coe_sub, inner_sub_left,
    positionCLM_inner, positionCLM_inner, momentumCLM_inner, momentumCLM_inner,
    ← inner_sub_right, ← Submodule.coe_sub, ← map_sub, angularMomentumCLM_eq_momentum_position]
  rfl

/-- Angular momentum on the Schwartz domain is densely defined and closable. -/
lemma angularMomentumOperator_isUnbounded :
    (angularMomentumOperator i j).IsUnbounded :=
  (angularMomentumOperator_isSymmetric i j).isUnbounded_iff_hasDenseDomain.mpr
    (angularMomentumOperator_hasDenseDomain i j)

/-!
## E. Commutation relations
-/

open Complex KroneckerDelta Bracket ContinuousLinearMap

variable (k l : Fin d) (ε : ℝˣ) (s : ℝ)

attribute [local instance 100] LieRing.ofAssociativeRing

/-!

### E.1. Angular momentum / position

-/

lemma angularMomentum_commutation_position :
    ⁅𝐋 i j, 𝐱 k⁆ = (I * ℏ) • (δ[i,k] • 𝐱 j - δ[j,k] • 𝐱 i) := by
  trans 𝐱 i ∘L ⁅𝐩 j, 𝐱 k⁆ - 𝐱 j ∘L ⁅𝐩 i, 𝐱 k⁆
  · simp [angularMomentumCLM, leibniz_lie]
  simp only [← lie_skew (𝐩 _), comp_neg, sub_neg_eq_add, add_comm, ← sub_eq_add_neg,
    position_commutation_momentum, comp_smul, comp_id, smul_sub, symm k _]

@[simp]
lemma angularMomentum_commutation_radiusRegPow : ⁅𝐋 i j, 𝐫₀[d] ε s⁆ = 0 := by
  trans 𝐱 i ∘L ⁅𝐩 j, 𝐫₀ ε s⁆ - 𝐱 j ∘L ⁅𝐩 i, 𝐫₀ ε s⁆
  · simp [angularMomentumCLM, leibniz_lie]
  simp [← lie_skew (𝐩 _), radiusRegPow_commutation_momentum, comp_neg,
    ← position_comp_radiusRegPow_commute, ← comp_assoc, position_comp_commute]

lemma angularMomentum_comp_radiusRegPow_commute : 𝐋 i j ∘L 𝐫₀ ε s = 𝐫₀ ε s ∘L 𝐋 i j := by
  rw [comp_eq_comp_add_commute, angularMomentum_commutation_radiusRegPow, add_zero]

@[simp]
lemma angularMomentumSqr_commutation_radiusRegPow : ⁅𝐋²[d], 𝐫₀[d] ε s⁆ = 0 := by
  simp [angularMomentumOperatorSqr, sum_lie, leibniz_lie]

lemma angularMomentumSqr_comp_radiusRegPow_commute : 𝐋² ∘L 𝐫₀[d] ε s = 𝐫₀ ε s ∘L 𝐋² := by
  rw [comp_eq_comp_add_commute, angularMomentumSqr_commutation_radiusRegPow, add_zero]

/-!

### E.2. Angular momentum / momentum

-/

lemma angularMomentum_commutation_momentum :
    ⁅𝐋 i j, 𝐩 k⁆ = (I * ℏ) • (δ[i,k] • 𝐩 j - δ[j,k] • 𝐩 i) := by
  trans ⁅𝐱 i, 𝐩 k⁆ ∘L 𝐩 j - ⁅𝐱 j, 𝐩 k⁆ ∘L 𝐩 i
  · simp [angularMomentumCLM, leibniz_lie]
  simp only [position_commutation_momentum, smul_comp, id_comp, smul_sub]

lemma momentum_comp_angularMomentum_eq :
    𝐩 k ∘L 𝐋 i j = 𝐋 i j ∘L 𝐩 k - (I * ℏ) • (δ[i,k] • 𝐩 j - δ[j,k] • 𝐩 i) := by
  rw [comp_eq_comp_sub_commute, angularMomentum_commutation_momentum]

@[simp]
lemma angularMomentum_commutation_momentumSqr : ⁅𝐋 i j, 𝐩[d] ⬝ᵥ 𝐩⁆ = 0 := by
  simp only [dotProduct, mul_def, lie_sum, lie_leibniz, angularMomentum_commutation_momentum,
    comp_smul, comp_sub, smul_comp, sub_comp, ← smul_add, ← Finset.smul_sum, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, sum_smul, sub_add_sub_cancel, sub_self, smul_zero]

lemma momentumSqr_comp_angularMomentum_commute : (𝐩 ⬝ᵥ 𝐩) ∘L 𝐋 i j = 𝐋 i j ∘L (𝐩 ⬝ᵥ 𝐩) := by
  rw [comp_eq_comp_sub_commute, angularMomentum_commutation_momentumSqr, sub_zero]

@[simp]
lemma angularMomentumSqr_commutation_momentumSqr : ⁅𝐋²[d], 𝐩[d] ⬝ᵥ 𝐩⁆ = 0 := by
  simp [angularMomentumOperatorSqr, sum_lie, leibniz_lie]

/-!

### E.3. Angular momentum / angular momentum

-/

lemma angularMomentum_commutation_angularMomentum : ⁅𝐋 i j, 𝐋 k l⁆ =
    (I * ℏ) • (δ[i,k] • 𝐋 j l - δ[i,l] • 𝐋 j k - δ[j,k] • 𝐋 i l + δ[j,l] • 𝐋 i k) := by
  nth_rw 2 [angularMomentumCLM]
  simp only [angularMomentum_commutation_position, angularMomentum_commutation_momentum,
    lie_sub, lie_leibniz, comp_smul, smul_comp, comp_sub, sub_comp, ← smul_add, ← smul_sub]
  dsimp [angularMomentumCLM]
  ext
  simp only [nsmul_eq_mul, smul_apply, sub_apply, add_apply, mul_apply_eq_comp, comp_apply,
    _root_.natCast_apply, positionCLM_apply, momentumCLM_apply, neg_mul, mul_neg, smul_neg,
    sub_neg_eq_add, smul_eq_mul, smul_add]
  ring

@[simp]
lemma angularMomentumSqr_commutation_angularMomentum : ⁅𝐋²[d], 𝐋 i j⁆ = 0 := by
  simp only [angularMomentumOperatorSqr, smul_lie, sum_lie, leibniz_lie, ← smul_add, comp_smul,
    comp_add, comp_sub, smul_comp, add_comp, sub_comp, angularMomentum_commutation_angularMomentum,
    angularMomentumCLM_antisymm _ i, angularMomentumCLM_antisymm j _, symm _ i, symm _ j,
    sum_smul, ← Finset.smul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  abel_nf
  simp [smul_zero]

end
end QuantumMechanics
