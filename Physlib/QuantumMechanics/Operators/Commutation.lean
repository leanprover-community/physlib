/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Physlib.Mathematics.KroneckerDelta.Basic
public import Physlib.Relativity.Tensors.RealTensor.Vector.Tensorial
public import Physlib.QuantumMechanics.Operators.AngularMomentum
/-!

# Commutation relations

## i. Overview

In this module we compute the commutators for common operators acting on Schwartz maps on `Space d`.

Commutator lemmas come in three flavors:
  - 1. `a_commutation_b` lemmas are of the form `⁅a, b⁆ = (⋯)`.
  - 2. `a_comp_b_commute` and `a_comp_commute` lemmas are of the form `a ∘ b = b ∘ a`.
  - 3. `a_comp_b_eq` lemmas are of the form `a ∘ b = b ∘ a + (⋯)`.

## ii. Key results

- `position_commutation_momentum` : The canonical commutation relations.
- `angularMomentum_commutation_position` : The position operator transforms as a vector under
    infinitessimal rotations.
- `angularMomentum_commutation_radiusRegPow` : Functions of `‖x‖²` commute with the angular momenta.
- `angularMomentum_commutation_momentum` : The momentum operator transforms as a vector under
    infinitessimal rotations.
- `angularMomentum_commutation_angularMomentum` : Angular momenta generate an `𝔰𝔬(d)` algebra.
- `angularMomentumSqr_commutation_angularMomentum` : `𝐋²` is a quadratic Casimir of `𝔰𝔬(d)`.

## iii. Table of contents

- A. General
- B. Commutators
  - B.1. Position / position
  - B.2. Momentum / momentum
  - B.3. Position / momentum
  - B.4. Angular momentum / position
  - B.5. Angular momentum / momentum
  - B.6. Angular momentum / angular momentum

## iv. References

* None.
-/

@[expose] public section

namespace QuantumMechanics
noncomputable section
open Complex Constants
open KroneckerDelta
open Bracket
open SchwartzMap ContinuousLinearMap

variable {d : ℕ} (i j k l : Fin d) (ε : ℝˣ) (s t : ℝ)

/-!

## A. General

-/

lemma leibniz_lie (A B C : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ)) :
    ⁅A ∘L B, C⁆ = A ∘L ⁅B, C⁆ + ⁅A, C⁆ ∘L B := by
  dsimp only [Bracket.bracket]
  simp only [ContinuousLinearMap.mul_def, comp_assoc, comp_sub, sub_comp, sub_add_sub_cancel]

lemma lie_leibniz (A B C : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ)) :
    ⁅A, B ∘L C⁆ = B ∘L ⁅A, C⁆ + ⁅A, B⁆ ∘L C := by
  dsimp only [Bracket.bracket]
  simp only [ContinuousLinearMap.mul_def, comp_assoc, comp_sub, sub_comp, sub_add_sub_cancel']

lemma comp_eq_comp_add_commute (A B : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ)) :
    A ∘L B = B ∘L A + ⁅A, B⁆ := by
  dsimp only [Bracket.bracket]
  simp only [ContinuousLinearMap.mul_def, add_sub_cancel]

/-- The identity commutes with everything. -/
lemma id_commutation (A : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ)) :
    ⁅ContinuousLinearMap.id ℂ 𝓢(Space d, ℂ), A⁆ = 0 := by
  rw [Ring.lie_def, ← ContinuousLinearMap.one_def, one_mul, mul_one, sub_self]

lemma comp_eq_comp_sub_commute (A B : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ)) :
    A ∘L B = B ∘L A - ⁅B, A⁆ := by
  dsimp only [Bracket.bracket]
  simp only [ContinuousLinearMap.mul_def, sub_sub_cancel]

/-!

## B. Commutators

-/

/-!

### B.1. Position / position

-/

/-- Position operators commute: `[xᵢ, xⱼ] = 0`. -/
@[simp]
lemma position_commutation_position : ⁅𝐱 i, 𝐱 j⁆ = 0 := by
  ext
  simp [bracket, ← mul_assoc, mul_comm]

lemma position_comp_commute : 𝐱 i ∘L 𝐱 j = 𝐱 j ∘L 𝐱 i := by
  rw [comp_eq_comp_add_commute, position_commutation_position, add_zero]

@[simp]
lemma position_commutation_radiusRegPow : ⁅𝐱 i, 𝐫₀[d] ε s⁆ = 0 := by
  ext
  simp [bracket, ← mul_assoc, mul_comm]

lemma position_comp_radiusRegPow_commute : 𝐱 i ∘L 𝐫₀ ε s = 𝐫₀ ε s ∘L 𝐱 i := by
  rw [comp_eq_comp_add_commute, position_commutation_radiusRegPow, add_zero]

@[simp]
lemma radiusRegPow_commutation_radiusRegPow : ⁅𝐫₀[d] ε s, 𝐫₀[d] ε t⁆ = 0 := by
  simp [bracket, mul_def, radiusRegPowCLM_comp_eq, add_comm]

/-!

### B.2. Momentum / momentum

-/

/-- Momentum operators commute: `[pᵢ, pⱼ] = 0`. -/
@[simp]
lemma momentum_commutation_momentum : ⁅𝐩 i, 𝐩 j⁆ = 0 := by
  ext ψ x
  have hdiff (k : Fin d) : Differentiable ℝ (∂[k] ψ) := Space.deriv_differentiable (ψ.smooth 2) k
  show 𝐩 i (𝐩 j ψ) x - 𝐩 j (𝐩 i ψ) x = 0
  simp only [momentumCLM_apply_fun, Space.deriv_const_smul _ (hdiff _),
    Space.deriv_commute _ (ψ.smooth 2), sub_self]

lemma momentum_comp_commute : 𝐩 i ∘L 𝐩 j = 𝐩 j ∘L 𝐩 i := by
  rw [comp_eq_comp_add_commute, momentum_commutation_momentum, add_zero]

attribute [local instance 100] LieRing.ofAssociativeRing

@[simp]
lemma momentumSqr_commutation_momentum : ⁅𝐩[d] ⬝ᵥ 𝐩, 𝐩 i⁆ = 0 := by
  simp [dotProduct, mul_def, sum_lie, leibniz_lie]

lemma momentumSqr_comp_momentum_commute : (𝐩 ⬝ᵥ 𝐩) ∘L 𝐩 i = 𝐩 i ∘L (𝐩 ⬝ᵥ 𝐩) := by
  rw [comp_eq_comp_add_commute, momentumSqr_commutation_momentum, add_zero]

/-!

### B.3. Position / momentum

-/

/-- The canonical commutation relations: `[xᵢ, pⱼ] = iℏ δᵢⱼ𝟙`. -/
lemma position_commutation_momentum : ⁅𝐱 i, 𝐩 j⁆ =
    (I * ℏ) • δ[i,j] • ContinuousLinearMap.id ℂ 𝓢(Space d, ℂ) := by
  ext ψ x
  show 𝐱 i (𝐩 j ψ) x - 𝐩 j (𝐱 i ψ) x = _
  trans (I * ℏ) * (-x i * ∂[j] ψ x + ∂[j] ((fun x : Space d ↦ x i) • ⇑ψ) x)
  · simp only [positionCLM_apply, momentumCLM_apply, positionCLM_apply_fun]
    ring
  rw [Space.deriv_smul (by fun_prop) (by fun_prop)]
  rw [Space.deriv_component]
  rcases eq_or_ne i j with (rfl | hne)
  · simp
  · simp [eq_zero_of_ne hne, hne.symm]

/-- The canonical commutation relations, pointwise: `xᵢ (pᵢ ψ)(x) - (pᵢ (xᵢ ψ))(x) = iℏ ψ(x)`. -/
lemma position_commutation_momentum_apply (ψ : 𝓢(Space d, ℂ)) (x : Space d) :
    ((x i : ℝ) : ℂ) * 𝐩 i ψ x - 𝐩 i (𝐱 i ψ) x = I * ℏ * ψ x := by
  have h := congrArg (fun T : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ) => T ψ x)
    (position_commutation_momentum (d := d) i i)
  simpa [Ring.lie_def, eq_one_of_same] using h

lemma momentum_comp_position_eq : 𝐩 j ∘L 𝐱 i =
    𝐱 i ∘L 𝐩 j - (I * ℏ) • δ[i,j] • ContinuousLinearMap.id ℂ 𝓢(Space d, ℂ) := by
  rw [comp_eq_comp_sub_commute, position_commutation_momentum]

lemma position_position_commutation_momentum : ⁅𝐱 i ∘L 𝐱 j, 𝐩 k⁆ =
    (I * ℏ) • (δ[i,k] • 𝐱 j + δ[j,k] • 𝐱 i) := by
  simp only [leibniz_lie, position_commutation_momentum, comp_smul, smul_comp, comp_id, id_comp,
    smul_add, add_comm]

lemma position_commutation_momentum_momentum : ⁅𝐱 i, 𝐩 j ∘L 𝐩 k⁆ =
    (I * ℏ) • (δ[i,k] • 𝐩 j + δ[i,j] • 𝐩 k) := by
  simp only [lie_leibniz, position_commutation_momentum, comp_smul, smul_comp, comp_id, id_comp,
    smul_add]

lemma position_commutation_momentumSqr : ⁅𝐱 i, 𝐩 ⬝ᵥ 𝐩⁆ = (2 * I * ℏ) • 𝐩 i := by
  simp only [dotProduct, mul_def, lie_sum, lie_leibniz, position_commutation_momentum, comp_smul,
    smul_comp, comp_id, id_comp, ← two_smul ℂ, smul_smul, mul_assoc, ← Finset.smul_sum, sum_smul]

lemma radiusRegPow_commutation_momentum :
    ⁅𝐫₀[d] ε s, 𝐩 i⁆ = (s * I * ℏ) • 𝐫₀ ε (s-2) ∘L 𝐱 i := by
  ext ψ x
  have hne := Ne.symm (ne_of_lt <| Space.norm_sq_add_unit_sq_pos ε x)
  have hdiff1 : DifferentiableAt ℝ (fun x => (‖x‖ ^ 2 + ↑ε ^ 2) ^ (s / 2)) x := by
    refine DifferentiableAt.rpow_const ?_ (Or.intro_left _ hne)
    exact Differentiable.differentiableAt (by fun_prop)
  have hdiff2 := Real.differentiableAt_rpow_const_of_ne (s / 2) hne
  have hdiff3 : DifferentiableAt ℝ (fun x ↦ ‖x‖ ^ 2 + ε ^ 2) x :=
    Differentiable.differentiableAt (by fun_prop)
  show 𝐫₀ ε s (𝐩 i ψ) x - 𝐩 i (𝐫₀ ε s ψ) x = (s * I * ℏ) * 𝐫₀ ε (s-2) (𝐱 i ψ) x
  simp only [momentumCLM_apply, positionCLM_apply, radiusRegPowCLM_apply_fun]
  rw [← Pi.smul_def', Space.deriv_smul hdiff1 (by fun_prop)]
  suffices ∂[i] (fun x ↦ (‖x‖ ^ 2 + ε ^ 2) ^ (s / 2)) x =
      s * (‖x‖ ^ 2 + ε ^ 2) ^ (s / 2 - 1) * x i by
    simp only [this, real_smul, ofReal_mul]
    ring_nf
  change ∂[i] ((fun r ↦ r ^ (s / 2)) ∘ (fun x ↦ ‖x‖ ^ 2 + ε ^ 2)) x = _
  rw [Space.deriv_eq, fderiv_comp x hdiff2 hdiff3, fderiv_add_const, fderiv_norm_sq_apply]
  simp [Real.deriv_rpow_const, mul_comm, ← mul_assoc, mul_div_cancel₀ s (NeZero.ne' 2).symm]

lemma momentum_comp_radiusRegPow_eq :
    𝐩 i ∘L 𝐫₀ ε s = 𝐫₀ ε s ∘L 𝐩 i - (s * I * ℏ) • 𝐫₀ ε (s-2) ∘L 𝐱 i := by
  rw [comp_eq_comp_sub_commute, radiusRegPow_commutation_momentum]

lemma radiusRegPow_commutation_momentumSqr :
    ⁅𝐫₀[d] ε s, 𝐩[d] ⬝ᵥ 𝐩⁆ = (2 * s * I * ℏ) • 𝐫₀ ε (s-2) ∘L (𝐱 ⬝ᵥ 𝐩)
    + (s * (d + s - 2) * ℏ ^ 2) • 𝐫₀ ε (s-2) - (ε ^ 2 * s * (s - 2) * ℏ ^ 2) • 𝐫₀ ε (s-4) := by
  calc
    _ = (s * I * ℏ) • ∑ i, ((𝐩 i ∘L 𝐫₀ ε (s-2)) ∘L 𝐱 i + 𝐫₀ ε (s-2) ∘L 𝐱 i ∘L 𝐩 i) := by
      simp [dotProduct, mul_def, lie_sum, lie_leibniz, radiusRegPow_commutation_momentum,
        ← smul_add, ← Finset.smul_sum, comp_assoc]
    _ = (s * I * ℏ) • ∑ i, (𝐫₀ ε (s-2) ∘L 𝐩 i ∘L 𝐱 i + 𝐫₀ ε (s-2) ∘L 𝐱 i ∘L 𝐩 i
        - (↑(s - 2) * I * ℏ) • 𝐫₀ ε (s-4) ∘L 𝐱 i ∘L 𝐱 i) := by
      simp only [momentum_comp_radiusRegPow_eq, sub_comp, smul_comp, sub_add_eq_add_sub, comp_assoc]
      ring_nf
    _ = (s * I * ℏ) • ∑ i, ((2 : ℂ) • 𝐫₀ ε (s-2) ∘L 𝐱 i ∘L 𝐩 i - (I * ℏ) • 𝐫₀ ε (s-2)
        - ((s - 2) * I * ℏ) • 𝐫₀ ε (s-4) ∘L 𝐱 i ∘L 𝐱 i) := by
      simp [momentum_comp_position_eq, sub_add_eq_add_sub, ← two_smul ℂ]
    _ = (s * I * ℏ) • ((2 : ℂ) • 𝐫₀ ε (s-2) ∘L (𝐱 ⬝ᵥ 𝐩) - (d * I * ℏ) • 𝐫₀ ε (s-2)
        - ((s - 2) * I * ℏ) • 𝐫₀ ε (s-4) ∘L ∑ i, 𝐱 i ∘L 𝐱 i) := by
      simp [Finset.sum_sub_distrib, ← Finset.smul_sum, ← comp_finsetSum,
        ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, dotProduct, mul_def, mul_assoc]
    _ = (2 * s * I * ℏ) • 𝐫₀ ε (s-2) ∘L (𝐱 ⬝ᵥ 𝐩) + (s * (d + s - 2) * ℏ ^ 2) • 𝐫₀ ε (s-2)
        - (ε ^ 2 * s * (s - 2) * ℏ ^ 2) • 𝐫₀ ε (s-4) := by
      simp_rw [positionSqCLM_eq ε, comp_sub, comp_smul, comp_id, radiusRegPowCLM_comp_eq]
      simp only [smul_sub, smul_smul, ← Complex.coe_smul, ofReal_mul, ofReal_add, ofReal_sub,
        ofReal_pow, ofReal_ofNat, ofReal_natCast]
      ring_nf
      simp_rw [← sub_add, sub_sub, ← add_smul, I_sq, sub_eq_add_neg, ← neg_smul]
      ring_nf

/-!

### B.4. Angular momentum / position

-/

lemma angularMomentum_commutation_position :
    ⁅𝐋 i j, 𝐱 k⁆ = (I * ℏ) • (δ[i,k] • 𝐱 j - δ[j,k] • 𝐱 i) := by
  trans 𝐱 i ∘L ⁅𝐩 j, 𝐱 k⁆ - 𝐱 j ∘L ⁅𝐩 i, 𝐱 k⁆
  · simp [angularMomentumOperator, leibniz_lie]
  simp only [← lie_skew (𝐩 _), comp_neg, sub_neg_eq_add, add_comm, ← sub_eq_add_neg,
    position_commutation_momentum, comp_smul, comp_id, smul_sub, symm k _]

@[simp]
lemma angularMomentum_commutation_radiusRegPow : ⁅𝐋 i j, 𝐫₀[d] ε s⁆ = 0 := by
  trans 𝐱 i ∘L ⁅𝐩 j, 𝐫₀ ε s⁆ - 𝐱 j ∘L ⁅𝐩 i, 𝐫₀ ε s⁆
  · simp [angularMomentumOperator, leibniz_lie]
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

### B.5. Angular momentum / momentum

-/

lemma angularMomentum_commutation_momentum :
    ⁅𝐋 i j, 𝐩 k⁆ = (I * ℏ) • (δ[i,k] • 𝐩 j - δ[j,k] • 𝐩 i) := by
  trans ⁅𝐱 i, 𝐩 k⁆ ∘L 𝐩 j - ⁅𝐱 j, 𝐩 k⁆ ∘L 𝐩 i
  · simp [angularMomentumOperator, leibniz_lie]
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

### B.6. Angular momentum / angular momentum

-/

lemma angularMomentum_commutation_angularMomentum : ⁅𝐋 i j, 𝐋 k l⁆ =
    (I * ℏ) • (δ[i,k] • 𝐋 j l - δ[i,l] • 𝐋 j k - δ[j,k] • 𝐋 i l + δ[j,l] • 𝐋 i k) := by
  nth_rw 2 [angularMomentumOperator]
  simp only [angularMomentum_commutation_position, angularMomentum_commutation_momentum,
    lie_sub, lie_leibniz, comp_smul, smul_comp, comp_sub, sub_comp, ← smul_add, ← smul_sub]
  dsimp [angularMomentumOperator]
  ext
  simp only [nsmul_eq_mul, smul_apply, sub_apply, add_apply, mul_apply_eq_comp, comp_apply,
    _root_.natCast_apply, positionCLM_apply, momentumCLM_apply, neg_mul, mul_neg, smul_neg,
    sub_neg_eq_add, smul_eq_mul, smul_add]
  ring

@[simp]
lemma angularMomentumSqr_commutation_angularMomentum : ⁅𝐋²[d], 𝐋 i j⁆ = 0 := by
  simp only [angularMomentumOperatorSqr, smul_lie, sum_lie, leibniz_lie, ← smul_add, comp_smul,
    comp_add, comp_sub, smul_comp, add_comp, sub_comp, angularMomentum_commutation_angularMomentum,
    angularMomentumOperator_antisymm _ i, angularMomentumOperator_antisymm j _, symm _ i, symm _ j,
    sum_smul, ← Finset.smul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  abel_nf
  simp [smul_zero]

end
end QuantumMechanics
