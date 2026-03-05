/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
import PhysLean.Mathematics.KroneckerDelta
import PhysLean.QuantumMechanics.DDimensions.Operators.AngularMomentum
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

-/

namespace QuantumMechanics
noncomputable section
open Complex Constants
open KroneckerDelta
open Bracket
open ContinuousLinearMap SchwartzMap

variable {d : ℕ} (i j k l : Fin d)

/-!

## A. General

-/

lemma leibniz_lie (A B C : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ)) :
    ⁅A ∘L B, C⁆ = A ∘L ⁅B, C⁆ + ⁅A, C⁆ ∘L B := by
  simp [bracket, mul_def, comp_assoc]

lemma lie_leibniz (A B C : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ)) :
    ⁅A, B ∘L C⁆ = B ∘L ⁅A, C⁆ + ⁅A, B⁆ ∘L C := by
  simp [bracket, mul_def, comp_assoc]

lemma comp_eq_comp_add_commute (A B : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ)) :
    A ∘L B = B ∘L A + ⁅A, B⁆ := by
  simp [bracket, mul_def]

lemma comp_eq_comp_sub_commute (A B : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ)) :
    A ∘L B = B ∘L A - ⁅B, A⁆ := by
  simp [bracket, mul_def]

/-!

## B. Commutators

-/

/-!

### B.1. Position / position

-/

/-- Position operators commute: `[xᵢ, xⱼ] = 0`. -/
@[simp]
lemma position_commutation_position : ⁅𝐱[i], 𝐱[j]⁆ = 0 := by
  ext
  simp [bracket, positionOperator_apply, ← mul_assoc, mul_comm]

lemma position_comp_commute : 𝐱[i] ∘L 𝐱[j] = 𝐱[j] ∘L 𝐱[i] := by
  rw [comp_eq_comp_add_commute, position_commutation_position, add_zero]

lemma position_commutation_radiusRegPow (hε : 0 < ε) (i : Fin d) :
    ⁅𝐱[i], radiusRegPowOperator (d := d) ε s⁆ = 0 := by
  ext
  simp [bracket, positionOperator_apply, radiusRegPowOperator_apply hε, ← mul_assoc, mul_comm]

lemma position_comp_radiusRegPow_commute (hε : 0 < ε) (i : Fin d) :
    𝐱[i] ∘L 𝐫[ε,s] = 𝐫[ε,s] ∘L 𝐱[i] := by
  rw [comp_eq_comp_add_commute, position_commutation_radiusRegPow hε, add_zero]

lemma radiusRegPow_commutation_radiusRegPow (hε : 0 < ε) :
    ⁅radiusRegPowOperator (d := d) ε s, radiusRegPowOperator (d := d) ε t⁆ = 0 := by
  simp [bracket, mul_def, radiusRegPowOperator_comp_eq hε, add_comm]

/-!

### B.2. Momentum / momentum

-/

/-- Momentum operators commute: `[pᵢ, pⱼ] = 0`. -/
@[simp]
lemma momentum_commutation_momentum : ⁅𝐩[i], 𝐩[j]⁆ = 0 := by
  ext ψ x
  have hdiff := Space.deriv_differentiable (ψ.smooth _)
  change 𝐩[i] (𝐩[j] ψ) x - 𝐩[j] (𝐩[i] ψ) x = 0
  simp only [momentumOperator_apply_fun, Space.deriv_const_smul _ (hdiff _), Pi.smul_apply,
    ← smul_sub, smul_smul]
  simp [Space.deriv_commute _ (ψ.smooth 2)]

lemma momentum_comp_commute : 𝐩[i] ∘L 𝐩[j] = 𝐩[j] ∘L 𝐩[i] := by
  rw [comp_eq_comp_add_commute, momentum_commutation_momentum, add_zero]

@[simp]
lemma momentumSqr_commutation_momentum : ⁅momentumOperatorSqr (d := d), 𝐩[i]⁆ = 0 := by
  simp [momentumOperatorSqr, sum_lie, leibniz_lie]

lemma momentumSqr_comp_momentum_commute : 𝐩² ∘L 𝐩[i] = 𝐩[i] ∘L 𝐩² := by
  rw [comp_eq_comp_add_commute, momentumSqr_commutation_momentum, add_zero]

/-!

### B.3. Position / momentum

-/

/-- The canonical commutation relations: `[xᵢ, pⱼ] = iℏ δᵢⱼ𝟙`. -/
lemma position_commutation_momentum : ⁅𝐱[i], 𝐩[j]⁆ =
    (I * ℏ * δ[i,j]) • ContinuousLinearMap.id ℂ 𝓢(Space d, ℂ) := by
  ext ψ x
  have hdiff : DifferentiableAt ℝ (fun x => x i) x := by
    have : (fun x ↦ x i) = ⇑(Space.coordCLM i) := by
      ext; rw [Space.coordCLM_apply, Space.coord_apply]
    rw [this]
    fun_prop
  change 𝐱[i] (𝐩[j] ψ) x - 𝐩[j] (𝐱[i] ψ) x = _
  trans (I * ℏ) * (-x i * ∂[j] ψ x + ∂[j] ((fun x : Space d ↦ x i) • ⇑ψ) x)
  · simp only [positionOperator_apply_fun, momentumOperator_apply_fun, Pi.smul_apply, smul_eq_mul]
    ring_nf
    rfl
  simp only [Space.deriv_smul hdiff ψ.differentiableAt, Space.deriv_component, ← kroneckerDelta_eq,
    kroneckerDelta_symm, real_smul, coe_smul', coe_id', Pi.smul_apply, id_eq,
    SchwartzMap.smul_apply, smul_eq_mul]
  ring

lemma momentum_comp_position_eq : 𝐩[j] ∘L 𝐱[i] =
    𝐱[i] ∘L 𝐩[j] - (I * ℏ * δ[i,j]) • ContinuousLinearMap.id ℂ 𝓢(Space d, ℂ) := by
  rw [comp_eq_comp_sub_commute, position_commutation_momentum]

lemma position_position_commutation_momentum : ⁅𝐱[i] ∘L 𝐱[j], 𝐩[k]⁆ =
    (I * ℏ * δ[i,k]) • 𝐱[j] + (I * ℏ * δ[j,k]) • 𝐱[i] := by
  simp [leibniz_lie, position_commutation_momentum, add_comm]

lemma position_commutation_momentum_momentum : ⁅𝐱[i], 𝐩[j] ∘L 𝐩[k]⁆ =
    (I * ℏ * δ[i,k]) • 𝐩[j] + (I * ℏ * δ[i,j]) • 𝐩[k] := by
  simp [lie_leibniz, position_commutation_momentum]

lemma position_commutation_momentumSqr : ⁅𝐱[i], 𝐩²⁆ = (2 * I * ℏ) • 𝐩[i] := by
  dsimp [momentumOperatorSqr]
  simp [lie_sum, lie_leibniz, position_commutation_momentum, ← two_smul ℂ, smul_smul, ← mul_assoc,
    sum_kroneckerDelta]

lemma radiusRegPow_commutation_momentum (hε : 0 < ε) (i : Fin d) :
    ⁅radiusRegPowOperator (d := d) ε s, 𝐩[i]⁆ = (s * I * ℏ) • 𝐫[ε,s-2] ∘L 𝐱[i] := by
  ext ψ x
  let g := fun r : ℝ ↦ Real.rpow r (s / 2)
  let normSqr_ε := fun x : Space d ↦ ‖x‖ ^ 2 + ε ^ 2
  have r_apply (φ : 𝓢(Space d, ℂ)) : 𝐫[ε,s] φ = (g ∘ normSqr_ε) • ⇑φ := by
    simp only [radiusRegPowOperator_apply_fun hε, g, normSqr_ε]
    rfl
  have hne : normSqr_ε x ≠ 0 := ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hε))
  have hg : DifferentiableAt ℝ g (normSqr_ε x) := Real.differentiableAt_rpow_const_of_ne (s / 2) hne
  have hderiv : ∂[i] (g ∘ normSqr_ε) x = s * (normSqr_ε x).rpow (s / 2 - 1) * x i := by
    rw [Space.deriv_eq, fderiv_comp x hg (by fun_prop)]
    dsimp [g, normSqr_ε]
    simp only [fderiv_add_const, fderiv_norm_sq_apply, fderiv_eq_smul_deriv, smul_eq_mul]
    rw [deriv_rpow_const (by fun_prop) (by left; exact hne)]
    simp only [coe_smul', coe_innerSL_apply, Pi.smul_apply, Space.inner_basis, deriv_id'']
    ring
  have hdiffAt : DifferentiableAt ℝ (g ∘ normSqr_ε) x := by
    refine DifferentiableAt.comp x hg ?_
    refine DifferentiableAt.add_const (ε ^ 2) ?_
    exact Differentiable.differentiableAt Space.norm_sq_differentiable

  change 𝐫[ε,s] (𝐩[i] ψ) x - 𝐩[i] (𝐫[ε,s] ψ) x = _
  simp only [momentumOperator_apply_fun, r_apply, Pi.smul_apply,
    Space.deriv_smul hdiffAt ψ.differentiableAt, hderiv]
  dsimp [g, normSqr_ε]
  simp only [positionOperator_apply_fun, radiusRegPowOperator_apply_fun hε, ofReal_mul, real_smul]
  ring_nf

lemma momentum_comp_radiusRegPow_eq (hε : 0 < ε) (i : Fin d) :
    𝐩[i] ∘L 𝐫[ε,s] = 𝐫[ε,s] ∘L 𝐩[i] - (s * I * ℏ) • 𝐫[ε,s-2] ∘L 𝐱[i] := by
  rw [comp_eq_comp_sub_commute, radiusRegPow_commutation_momentum hε]

lemma radiusRegPow_commutation_momentumSqr (hε : 0 < ε) :
    ⁅radiusRegPowOperator (d := d) ε s, momentumOperatorSqr (d := d)⁆ =
    (2 * s * I * ℏ) • 𝐫[ε,s-2] ∘L ∑ i, 𝐱[i] ∘L 𝐩[i] + (s * (d + s - 2) * ℏ ^ 2) • 𝐫[ε,s-2]
    - (ε ^ 2 * s * (s - 2) * ℏ ^ 2) • 𝐫[ε,s-4] := by
  dsimp [momentumOperatorSqr]
  simp only [lie_sum, lie_leibniz, radiusRegPow_commutation_momentum hε, comp_smul, smul_comp,
    ← smul_add, ← comp_assoc, momentum_comp_radiusRegPow_eq hε, sub_comp, smul_comp]
  simp only [comp_assoc, momentum_comp_position_eq, comp_sub, comp_smul, comp_id,
    ← Finset.smul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← comp_finset_sum,
    positionOperatorSqr_eq hε, comp_sub, radiusRegPowOperator_comp_eq hε, sum_kroneckerDelta_self]
  ext
  simp only [ofReal_sub, coe_smul', Pi.smul_apply, ContinuousLinearMap.add_apply, coe_sub',
    Pi.sub_apply, SchwartzMap.smul_apply, SchwartzMap.add_apply, SchwartzMap.sub_apply, smul_eq_mul,
    real_smul, ofReal_pow, ofReal_mul, ofReal_add, ofReal_natCast]
  ring_nf
  simp only [I_sq]
  ring

/-!

### B.4. Angular momentum / position

-/

lemma angularMomentum_commutation_position : ⁅𝐋[i,j], 𝐱[k]⁆ =
    (I * ℏ * δ[i,k]) • 𝐱[j] - (I * ℏ * δ[j,k]) • 𝐱[i] := by
  dsimp [angularMomentumOperator]
  simp only [sub_lie, leibniz_lie, ← lie_skew 𝐩[_] 𝐱[_], position_commutation_momentum]
  simp [kroneckerDelta_symm, add_comm, sub_eq_add_neg]

lemma angularMomentum_commutation_radiusRegPow (hε : 0 < ε) (i j : Fin d) :
    ⁅𝐋[i,j], radiusRegPowOperator (d := d) ε s⁆ = 0 := by
  dsimp [angularMomentumOperator]
  simp only [sub_lie, leibniz_lie, ← lie_skew 𝐩[_] _, radiusRegPow_commutation_momentum hε,
    position_commutation_radiusRegPow hε]
  simp [comp_neg, ← position_comp_radiusRegPow_commute hε, ← comp_assoc, position_comp_commute i j]

lemma angularMomentumSqr_commutation_radiusRegPow (hε : 0 < ε) :
    ⁅angularMomentumOperatorSqr (d := d), radiusRegPowOperator (d := d) ε s⁆ = 0 := by
  dsimp [angularMomentumOperatorSqr]
  simp [sum_lie, leibniz_lie, angularMomentum_commutation_radiusRegPow hε]

/-!

### B.5. Angular momentum / momentum

-/

lemma angularMomentum_commutation_momentum : ⁅𝐋[i,j], 𝐩[k]⁆ =
    (I * ℏ * δ[i,k]) • 𝐩[j] - (I * ℏ * δ[j,k]) • 𝐩[i] := by
  dsimp [angularMomentumOperator]
  simp [sub_lie, leibniz_lie, position_commutation_momentum]

lemma momentum_comp_angularMomentum_eq : 𝐩[k] ∘L 𝐋[i,j] =
    𝐋[i,j] ∘L 𝐩[k] - (I * ℏ * δ[i,k]) • 𝐩[j] + (I * ℏ * δ[j,k]) • 𝐩[i] := by
  rw [comp_eq_comp_sub_commute, angularMomentum_commutation_momentum, sub_add]

@[simp]
lemma angularMomentum_commutation_momentumSqr : ⁅𝐋[i,j], momentumOperatorSqr (d := d)⁆ = 0 := by
  dsimp [momentumOperatorSqr]
  simp [lie_sum, lie_leibniz, angularMomentum_commutation_momentum, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, sum_kroneckerDelta]

lemma momentumSqr_comp_angularMomentum_commute : 𝐩² ∘L 𝐋[i,j] = 𝐋[i,j] ∘L 𝐩² := by
  rw [comp_eq_comp_sub_commute, angularMomentum_commutation_momentumSqr, sub_zero]

@[simp]
lemma angularMomentumSqr_commutation_momentumSqr :
    ⁅angularMomentumOperatorSqr (d := d), momentumOperatorSqr (d := d)⁆ = 0 := by
  dsimp [angularMomentumOperatorSqr]
  simp [sum_lie, leibniz_lie]

/-!

### B.6. Angular momentum / angular momentum

-/

lemma angularMomentum_commutation_angularMomentum : ⁅𝐋[i,j], 𝐋[k,l]⁆ =
    (I * ℏ * δ[i,k]) • 𝐋[j,l] - (I * ℏ * δ[i,l]) • 𝐋[j,k]
    - (I * ℏ * δ[j,k]) • 𝐋[i,l] + (I * ℏ * δ[j,l]) • 𝐋[i,k] := by
  nth_rw 2 [angularMomentumOperator]
  simp only [lie_sub, lie_leibniz, angularMomentum_commutation_position,
    angularMomentum_commutation_momentum]
  dsimp [angularMomentumOperator]
  ext
  simp only [comp_sub, comp_smulₛₗ, RingHom.id_apply, coe_sub', Pi.sub_apply,
    ContinuousLinearMap.add_apply, coe_smul', coe_comp', Pi.smul_apply, Function.comp_apply,
    SchwartzMap.sub_apply, SchwartzMap.add_apply, SchwartzMap.smul_apply, smul_eq_mul]
  ring

@[simp]
lemma angularMomentumSqr_commutation_angularMomentum :
    ⁅angularMomentumOperatorSqr (d := d), 𝐋[i,j]⁆ = 0 := by
  dsimp [angularMomentumOperatorSqr]
  simp only [smul_lie, sum_lie, leibniz_lie, angularMomentum_commutation_angularMomentum,
    comp_add, comp_sub, add_comp, sub_comp, comp_smul, smul_comp, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  -- Swap order of sums so that inner sum always involves δ
  nth_rw 1 [Finset.sum_comm]
  nth_rw 2 [Finset.sum_comm]
  nth_rw 5 [Finset.sum_comm]
  nth_rw 6 [Finset.sum_comm]
  simp only [sum_kroneckerDelta', angularMomentumOperator_antisymm _ i,
    angularMomentumOperator_antisymm j _, comp_neg, neg_comp, smul_neg, neg_neg,
    Finset.sum_neg_distrib, ← sub_eq_add_neg, sub_neg_eq_add]
  ext
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.zero_apply, SchwartzMap.smul_apply,
    SchwartzMap.add_apply, SchwartzMap.sub_apply, SchwartzMap.zero_apply, smul_eq_mul]
  ring

end
end QuantumMechanics
