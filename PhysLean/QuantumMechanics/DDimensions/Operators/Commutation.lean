/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import PhysLean.Mathematics.KroneckerDelta
public import PhysLean.QuantumMechanics.DDimensions.Operators.AngularMomentum
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

private lemma ite_cond_symm (i j : Fin d) :
    (if i = j then A else B) = (if j = i then A else B) :=
  ite_cond_congr (Eq.propIntro Eq.symm Eq.symm)

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
lemma position_commutation_position : ⁅𝐱[i], 𝐱[j]⁆ = 0 := by
  ext
  simp [bracket, ← mul_assoc, mul_comm]

lemma position_comp_commute : 𝐱[i] ∘L 𝐱[j] = 𝐱[j] ∘L 𝐱[i] := by
  rw [comp_eq_comp_add_commute, position_commutation_position, add_zero]

@[simp]
lemma position_commutation_radiusRegPow : ⁅𝐱[i], 𝐫[d,ε,s]⁆ = 0 := by
  ext
  simp [bracket, ← mul_assoc, mul_comm]

lemma position_comp_radiusRegPow_commute : 𝐱[i] ∘L 𝐫[ε,s] = 𝐫[ε,s] ∘L 𝐱[i] := by
  rw [comp_eq_comp_add_commute, position_commutation_radiusRegPow, add_zero]

@[simp]
lemma radiusRegPow_commutation_radiusRegPow : ⁅𝐫[d,ε,s], 𝐫[d,ε,t]⁆ = 0 := by
  simp [bracket, mul_def, radiusRegPowOperator_comp_eq, add_comm]

/-!

### B.2. Momentum / momentum

-/

/-- Momentum operators commute: `[pᵢ, pⱼ] = 0`. -/
@[simp]
lemma momentum_commutation_momentum : ⁅𝐩[i], 𝐩[j]⁆ = 0 := by
  ext ψ x
  have hdiff (k : Fin d) : Differentiable ℝ (∂[k] ψ) := Space.deriv_differentiable (ψ.smooth 2) k
  show 𝐩[i] (𝐩[j] ψ) x - 𝐩[j] (𝐩[i] ψ) x = 0
  simp only [momentumOperator_apply_fun, Space.deriv_const_smul _ (hdiff _),
    Space.deriv_commute _ (ψ.smooth 2), sub_self]

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
    (I * ℏ) • δ[i,j] • ContinuousLinearMap.id ℂ 𝓢(Space d, ℂ) := by
  ext ψ x
  show 𝐱[i] (𝐩[j] ψ) x - 𝐩[j] (𝐱[i] ψ) x = _
  trans (I * ℏ) * (-x i * ∂[j] ψ x + ∂[j] ((fun x : Space d ↦ x i) • ⇑ψ) x)
  · simp only [positionOperator_apply, momentumOperator_apply, positionOperator_apply_fun]
    ring
  rw [Space.deriv_smul (by fun_prop) (by fun_prop)]
  rw [Space.deriv_component]
  rcases eq_or_ne i j with (rfl | hne)
  · simp
  · simp [eq_zero_of_ne hne, hne.symm]

lemma momentum_comp_position_eq : 𝐩[j] ∘L 𝐱[i] =
    𝐱[i] ∘L 𝐩[j] - (I * ℏ) • δ[i,j] • ContinuousLinearMap.id ℂ 𝓢(Space d, ℂ) := by
  rw [comp_eq_comp_sub_commute, position_commutation_momentum]

lemma position_position_commutation_momentum : ⁅𝐱[i] ∘L 𝐱[j], 𝐩[k]⁆ =
    (I * ℏ) • (δ[i,k] • 𝐱[j] + δ[j,k] • 𝐱[i]) := by
  simp only [leibniz_lie, position_commutation_momentum, comp_smul, smul_comp, comp_id, id_comp,
    smul_add, add_comm]

lemma position_commutation_momentum_momentum : ⁅𝐱[i], 𝐩[j] ∘L 𝐩[k]⁆ =
    (I * ℏ) • (δ[i,k] • 𝐩[j] + δ[i,j] • 𝐩[k]) := by
  simp only [lie_leibniz, position_commutation_momentum, comp_smul, smul_comp, comp_id, id_comp,
    smul_add]

lemma position_commutation_momentumSqr : ⁅𝐱[i], 𝐩²⁆ = (2 * I * ℏ) • 𝐩[i] := by
  simp only [momentumOperatorSqr, lie_sum, lie_leibniz, position_commutation_momentum, comp_smul,
    smul_comp, comp_id, id_comp, ← two_smul ℂ, smul_smul, mul_assoc, ← Finset.smul_sum, sum_smul]

lemma radiusRegPow_commutation_momentum :
    ⁅𝐫[d,ε,s], 𝐩[i]⁆ = (s * I * ℏ) • 𝐫[ε,s-2] ∘L 𝐱[i] := by
  dsimp only [Bracket.bracket]
  ext ψ x
  simp only [coe_sub', coe_mul, Pi.sub_apply, Function.comp_apply, SchwartzMap.sub_apply, coe_smul',
    coe_comp', Pi.smul_apply, SchwartzMap.smul_apply, smul_eq_mul]
  simp only [momentumOperator_apply, positionOperator_apply, radiusRegPowOperator_apply_fun]

  have hne : ∀ x : Space d, ‖x‖ ^ 2 + ε ^ 2 ≠ 0 := by
    intro x
    apply ne_of_gt
    exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_iff.mpr <| Units.ne_zero ε)

  have h : (fun x ↦ (‖x‖ ^ 2 + ε ^ 2) ^ (s / 2) • ψ x) =
    (fun (x : Space d) ↦ (‖x‖ ^ 2 + ε ^ 2) ^ (s / 2)) • ψ := rfl
  have h' : ∂[i] (fun x ↦ (‖x‖ ^ 2 + ε ^ 2) ^ (s / 2)) =
      fun x ↦ s * (‖x‖ ^ 2 + ε ^ 2) ^ (s / 2 - 1) * x i := by
    trans ∂[i] ((fun x ↦ x ^ (s / 2)) ∘ (fun x ↦ ‖x‖ ^ 2 + ε ^ 2))
    · congr
    ext x
    rw [Space.deriv_eq, fderiv_comp]
    · simp only [fderiv_add_const, fderiv_norm_sq_apply, comp_smul, coe_smul', coe_comp',
        coe_innerSL_apply, Pi.smul_apply, Function.comp_apply, Space.inner_basis,
        fderiv_eq_smul_deriv, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat]
      rw [deriv_rpow_const]
      · simp only [deriv_id'', one_mul]
        ring
      · fun_prop
      · left
        exact hne _
    · exact Real.differentiableAt_rpow_const_of_ne (s / 2) (hne x)
    · exact Differentiable.differentiableAt (by fun_prop)

  rw [h, Space.deriv_smul]
  · rw [h']
    simp only [neg_mul, smul_neg, Complex.real_smul, Complex.ofReal_mul, sub_neg_eq_add]
    ring_nf
  · refine DifferentiableAt.rpow ?_ (by fun_prop) (hne _)
    exact Differentiable.differentiableAt (by fun_prop)
  · fun_prop

lemma momentum_comp_radiusRegPow_eq :
    𝐩[i] ∘L 𝐫[ε,s] = 𝐫[ε,s] ∘L 𝐩[i] - (s * I * ℏ) • 𝐫[ε,s-2] ∘L 𝐱[i] := by
  rw [comp_eq_comp_sub_commute, radiusRegPow_commutation_momentum]

lemma radiusRegPow_commutation_momentumSqr :
    ⁅𝐫[d,ε,s], momentumOperatorSqr (d := d)⁆ = (2 * s * I * ℏ) • 𝐫[ε,s-2] ∘L ∑ i, 𝐱[i] ∘L 𝐩[i]
    + (s * (d + s - 2) * ℏ ^ 2) • 𝐫[ε,s-2] - (ε ^ 2 * s * (s - 2) * ℏ ^ 2) • 𝐫[ε,s-4] := by
  calc
    _ = (s * I * ℏ) • ∑ i, ((𝐩[i] ∘L 𝐫[ε,s-2]) ∘L 𝐱[i] + 𝐫[ε,s-2] ∘L 𝐱[i] ∘L 𝐩[i]) := by
      simp [momentumOperatorSqr, lie_sum, lie_leibniz, radiusRegPow_commutation_momentum,
        ← smul_add, ← Finset.smul_sum, comp_assoc]
    _ = (s * I * ℏ) • ∑ i, (𝐫[ε,s-2] ∘L 𝐩[i] ∘L 𝐱[i] + 𝐫[ε,s-2] ∘L 𝐱[i] ∘L 𝐩[i]
        - (↑(s - 2) * I * ℏ) • 𝐫[ε,s-4] ∘L 𝐱[i] ∘L 𝐱[i]) := by
      simp only [momentum_comp_radiusRegPow_eq, sub_comp, smul_comp, sub_add_eq_add_sub, comp_assoc]
      ring_nf
    _ = (s * I * ℏ) • ∑ i, ((2 : ℂ) • 𝐫[ε,s-2] ∘L 𝐱[i] ∘L 𝐩[i] - (I * ℏ) • 𝐫[ε,s-2]
        - (↑(s - 2) * I * ℏ) • 𝐫[ε,s-4] ∘L 𝐱[i] ∘L 𝐱[i]) := by
      simp [momentum_comp_position_eq, sub_add_eq_add_sub, ← two_smul ℂ]
  simp only [Finset.sum_sub_distrib, ← Finset.smul_sum, smul_sub, smul_smul, ← comp_finset_sum]
  have hsumr : ∑ i : Fin d, 𝐫[d,ε,s-2] = (d : ℂ) • 𝐫[ε,s-2] := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.cast_smul_eq_nsmul]
  have hrxx : 𝐫[d,ε,s-4] ∘L ∑ i, 𝐱[i] ∘L 𝐱[i] = 𝐫[ε,s-2] - (ε ^ 2 : ℂ) • 𝐫[ε,s-4] := by
    rw [positionOperatorSqr_eq ε, comp_sub, comp_smul, comp_id, radiusRegPowOperator_comp_eq,
      ← Complex.coe_smul (ε.1 ^ 2), ofReal_pow]
    ring_nf
  rw [hsumr, hrxx, smul_smul, smul_sub, ← sub_add, sub_sub, ← add_smul, smul_smul]
  simp only [sub_eq_add_neg, ← neg_smul]
  congr 3 -- match coefficients of `r[s-4]∑xᵢpᵢ`, `r[s-2]` and `r[s-4]`
  · ring
  · ring_nf
    simp only [I_sq, ofReal_add, ofReal_neg, RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe,
      MonoidHom.toOneHom_coe, MonoidHom.coe_coe, coe_algebraMap, ZeroHom.coe_mk, ofReal_sub,
      ofReal_mul, ofReal_natCast, ofReal_pow]
    ring
  · ring_nf
    simp only [I_sq, ofReal_add, ofReal_neg, RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe,
      MonoidHom.toOneHom_coe, MonoidHom.coe_coe, coe_algebraMap, ZeroHom.coe_mk, ofReal_sub,
      ofReal_mul, ofReal_pow]
    ring

/-!

### B.4. Angular momentum / position

-/

lemma angularMomentum_commutation_position :
    ⁅𝐋[i,j], 𝐱[k]⁆ = (I * ℏ) • (δ[i,k] • 𝐱[j] - δ[j,k] • 𝐱[i]) := by
  trans 𝐱[i] ∘L ⁅𝐩[j], 𝐱[k]⁆ - 𝐱[j] ∘L ⁅𝐩[i], 𝐱[k]⁆
  · simp [angularMomentumOperator, leibniz_lie]
  simp only [← lie_skew 𝐩[_] 𝐱[_], comp_neg, sub_neg_eq_add, add_comm, ← sub_eq_add_neg,
    position_commutation_momentum, comp_smul, comp_id, smul_sub, symm k _]

@[simp]
lemma angularMomentum_commutation_radiusRegPow : ⁅𝐋[i,j], 𝐫[d,ε,s]⁆ = 0 := by
  trans 𝐱[i] ∘L ⁅𝐩[j], 𝐫[ε,s]⁆ - 𝐱[j] ∘L ⁅𝐩[i], 𝐫[ε,s]⁆
  · simp [angularMomentumOperator, leibniz_lie]
  simp [← lie_skew 𝐩[_] 𝐫[_,_], radiusRegPow_commutation_momentum, comp_neg,
    ← position_comp_radiusRegPow_commute, ← comp_assoc, position_comp_commute]

@[simp]
lemma angularMomentumSqr_commutation_radiusRegPow :
    ⁅angularMomentumOperatorSqr (d := d), 𝐫[d,ε,s]⁆ = 0 := by
  simp [angularMomentumOperatorSqr, sum_lie, leibniz_lie]

/-!

### B.5. Angular momentum / momentum

-/

lemma angularMomentum_commutation_momentum : ⁅𝐋[i,j], 𝐩[k]⁆ =
    (I * ℏ) • (δ[i,k] • 𝐩[j] - δ[j,k] • 𝐩[i]) := by
  trans ⁅𝐱[i], 𝐩[k]⁆ ∘L 𝐩[j] - ⁅𝐱[j], 𝐩[k]⁆ ∘L 𝐩[i]
  · simp [angularMomentumOperator, leibniz_lie]
  simp only [position_commutation_momentum, smul_comp, id_comp, smul_sub]

lemma momentum_comp_angularMomentum_eq : 𝐩[k] ∘L 𝐋[i,j] =
    𝐋[i,j] ∘L 𝐩[k] - (I * ℏ) • (δ[i,k] • 𝐩[j] - δ[j,k] • 𝐩[i]) := by
  rw [comp_eq_comp_sub_commute, angularMomentum_commutation_momentum]

@[simp]
lemma angularMomentum_commutation_momentumSqr : ⁅𝐋[i,j], momentumOperatorSqr (d := d)⁆ = 0 := by
  simp only [momentumOperatorSqr, lie_sum, lie_leibniz, angularMomentum_commutation_momentum,
    comp_smul, comp_sub, smul_comp, sub_comp, ← smul_add, ← Finset.smul_sum, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, sum_smul, sub_add_sub_cancel, sub_self, smul_zero]

lemma momentumSqr_comp_angularMomentum_commute : 𝐩² ∘L 𝐋[i,j] = 𝐋[i,j] ∘L 𝐩² := by
  rw [comp_eq_comp_sub_commute, angularMomentum_commutation_momentumSqr, sub_zero]

@[simp]
lemma angularMomentumSqr_commutation_momentumSqr :
    ⁅angularMomentumOperatorSqr (d := d), momentumOperatorSqr (d := d)⁆ = 0 := by
  simp [angularMomentumOperatorSqr, sum_lie, leibniz_lie]

/-!

### B.6. Angular momentum / angular momentum

-/

@[sorryful]
lemma angularMomentum_commutation_angularMomentum {d : ℕ} (i j k l : Fin d) : ⁅𝐋[i,j], 𝐋[k,l]⁆ =
    (Complex.I * ℏ * δ[i,k]) • 𝐋[j,l] - (Complex.I * ℏ * δ[i,l]) • 𝐋[j,k]
    - (Complex.I * ℏ * δ[j,k]) • 𝐋[i,l] + (Complex.I * ℏ * δ[j,l]) • 𝐋[i,k] := by
  nth_rw 2 [angularMomentumOperator]
  rw [lie_sub]
  rw [lie_leibniz, lie_leibniz]
  rw [angularMomentum_commutation_momentum, angularMomentum_commutation_position]
  rw [angularMomentum_commutation_momentum, angularMomentum_commutation_position]
  dsimp only [angularMomentumOperator, kroneckerDelta]
  simp only [ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp,
    ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp]
  ext ψ x
  simp only [coe_sub', Pi.sub_apply, ContinuousLinearMap.add_apply, SchwartzMap.sub_apply,
    SchwartzMap.add_apply, smul_sub]
  ring_nf
  sorry

@[sorryful]
lemma angularMomentumSqr_commutation_angularMomentum {d : ℕ} (i j : Fin d) :
    ⁅angularMomentumOperatorSqr (d := d), 𝐋[i,j]⁆ = 0 := by
  sorry

end
end QuantumMechanics
