/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.SpaceAndTime.Space.Derivatives.Basic
/-!

# Lorentz group actions related to SpaceTime

## i. Overview

We already have a Lorentz group action on `SpaceTime d`, in this module
we define the induced action on Schwartz functions and distributions.

## ii. Key results

- `schwartzAction` : Defines the action of the Lorentz group on Schwartz functions.
- An instance of `DistribMulAction` for the Lorentz group acting on distributions.

## iii. Table of contents

- A. Lorentz group action on Schwartz functions
  - A.1. The definition of the action
  - A.2. Basic properties of the action
  - A.3. Injectivity of the action
  - A.4. Surjectivity of the action
- B. Lorentz group action on distributions
  - B.1. The SMul instance
  - B.2. The DistribMulAction instance
  - B.3. The SMulCommClass instance
  - B.4. Action as a linear map

## iv. References

-/
noncomputable section

namespace SpaceTime

open Manifold
open Matrix
open Complex
open ComplexConjugate
open TensorSpecies
open SchwartzMap
attribute [-simp] Fintype.sum_sum_type

/-!

## A. Lorentz group action on Schwartz functions

-/

/-!

### A.1. The definition of the action

-/

/-- The Lorentz group action on Schwartz functions taking the Lorentz group to
  continuous linear maps. -/
def schwartzAction {d} : LorentzGroup d →* 𝓢(SpaceTime d, ℝ) →L[ℝ] 𝓢(SpaceTime d, ℝ) where
  toFun Λ := SchwartzMap.compCLM (𝕜 := ℝ)
    (Lorentz.Vector.actionCLM Λ⁻¹).hasTemperateGrowth <| by
      use 1, ‖Lorentz.Vector.actionCLM Λ‖
      simp only [pow_one]
      intro x
      obtain ⟨x, rfl⟩ := Lorentz.Vector.actionCLM_surjective Λ x
      apply (ContinuousLinearMap.le_opNorm (Lorentz.Vector.actionCLM Λ) x).trans
      simp [Lorentz.Vector.actionCLM_apply, mul_add]
  map_one' := by
    ext η x
    simp [Lorentz.Vector.actionCLM_apply]
  map_mul' Λ₁ Λ₂ := by
    ext η x
    simp only [_root_.mul_inv_rev, compCLM_apply, Function.comp_apply,
      Lorentz.Vector.actionCLM_apply, ContinuousLinearMap.coe_mul]
    rw [SemigroupAction.mul_smul]

/-!

### A.2. Basic properties of the action

-/

lemma schwartzAction_mul_apply {d} (Λ₁ Λ₂ : LorentzGroup d)
    (η : 𝓢(SpaceTime d, ℝ)) :
    schwartzAction Λ₂ (schwartzAction (Λ₁) η) =
    schwartzAction (Λ₂ * Λ₁) η := by
  simp

lemma schwartzAction_apply {d} (Λ : LorentzGroup d)
    (η : 𝓢(SpaceTime d, ℝ)) (x : SpaceTime d) :
    (schwartzAction Λ η) x = η (Λ⁻¹ • x) := rfl

/-!

### A.3. Injectivity of the action

-/

lemma schwartzAction_injective {d} (Λ : LorentzGroup d) :
    Function.Injective (schwartzAction Λ) := by
  intro η1 η2 h
  ext x
  have h1 : (schwartzAction Λ⁻¹ * schwartzAction Λ) η1 =
    (schwartzAction Λ⁻¹ * schwartzAction Λ) η2 := by simp [h]
  rw [← map_mul] at h1
  simp at h1
  rw [h1]

/-!

### A.4. Surjectivity of the action

-/

lemma schwartzAction_surjective {d} (Λ : LorentzGroup d) :
    Function.Surjective (schwartzAction Λ) := by
  intro η
  use (schwartzAction Λ⁻¹ η)
  change (schwartzAction Λ * schwartzAction Λ⁻¹) η = _
  rw [← map_mul]
  simp

/-!

## B. Lorentz group action on distributions

-/
section Distribution

/-!

### B.1. The SMul instance

-/
variable
    {c : Fin n → realLorentzTensor.Color} {M : Type} [NormedAddCommGroup M]
      [NormedSpace ℝ M] [Tensorial (realLorentzTensor d) c M] [T2Space M]

open Distribution
instance : SMul (LorentzGroup d) ((SpaceTime d) →d[ℝ] M) where
  smul Λ f := (Tensorial.actionCLM (realLorentzTensor d) Λ) ∘L f ∘L (schwartzAction Λ⁻¹)

lemma lorentzGroup_smul_dist_apply (Λ : LorentzGroup d) (f : (SpaceTime d) →d[ℝ] M)
    (η : 𝓢(SpaceTime d, ℝ)) : (Λ • f) η = Λ • (f (schwartzAction Λ⁻¹ η)) := rfl

/-!

### B.2. The DistribMulAction instance

-/

instance : DistribMulAction (LorentzGroup d) ((SpaceTime d) →d[ℝ] M) where
  one_smul f := by
    ext η
    simp [lorentzGroup_smul_dist_apply]
  mul_smul Λ₁ Λ₂ f := by
    ext η
    simp [lorentzGroup_smul_dist_apply, SemigroupAction.mul_smul]
  smul_zero Λ := by
    ext η
    rw [lorentzGroup_smul_dist_apply]
    simp
  smul_add Λ f1 f2 := by
    ext η
    simp [ContinuousLinearMap.add_apply, smul_add, lorentzGroup_smul_dist_apply]

/-!

### B.3. The SMulCommClass instance

-/

instance : SMulCommClass ℝ (LorentzGroup d) ((SpaceTime d) →d[ℝ] M) where
  smul_comm a Λ f := by
    ext η
    simp [lorentzGroup_smul_dist_apply]
    rw [SMulCommClass.smul_comm]

/-!

### B.4. Action as a linear map

-/

/-- The Lorentz action on distributions as a linear map. -/
def distActionLinearMap {d} {M : Type} [NormedAddCommGroup M]
    [NormedSpace ℝ M] [Tensorial (realLorentzTensor d) c M] [T2Space M](Λ : LorentzGroup d) :
    ((SpaceTime d) →d[ℝ] M) →ₗ[ℝ] ((SpaceTime d) →d[ℝ] M) where
  toFun f := Λ • f
  map_add' f1 f2 := by
    ext η
    simp [lorentzGroup_smul_dist_apply, ContinuousLinearMap.add_apply, smul_add]
  map_smul' a f := by
    ext η
    simp [lorentzGroup_smul_dist_apply]
    rw [← @smul_comm]
end Distribution
end SpaceTime

end
