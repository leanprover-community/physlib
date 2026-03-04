/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
import PhysLean.Mathematics.KroneckerDelta
import PhysLean.QuantumMechanics.DDimensions.Operators.AngularMomentum
/-!

# Commutation relations

-/

namespace QuantumMechanics
noncomputable section
open Complex Constants
open KroneckerDelta
open Bracket
open ContinuousLinearMap SchwartzMap

variable {d : ℕ} (i j k l : Fin d)

private lemma ite_cond_symm (i j : Fin d) :
    (if i = j then A else B) = (if j = i then A else B) :=
  ite_cond_congr (Eq.propIntro Eq.symm Eq.symm)

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

/-
## Position / position commutators
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

/-
## Momentum / momentum commutators
-/

/-- Momentum operators commute: `[pᵢ, pⱼ] = 0`. -/
@[simp]
lemma momentum_commutation_momentum : ⁅𝐩[i], 𝐩[j]⁆ = 0 := by
  ext ψ x
  have hdiff := Space.deriv_differentiable (ψ.smooth _)
  calc
    _ = 𝐩[i] (𝐩[j] ψ) x - 𝐩[j] (𝐩[i] ψ) x := by
      simp [bracket]
    _ = (-I * ℏ) ^ 2 • (∂[i] (∂[j] ψ) x - ∂[j] (∂[i] ψ) x) := by
      simp only [momentumOperator_apply_fun, Space.deriv_const_smul _ (hdiff _), Pi.smul_apply,
        ← smul_sub, smul_smul, pow_two]
  simp [Space.deriv_commute _ (ψ.smooth 2)]

lemma momentum_comp_commute : 𝐩[i] ∘L 𝐩[j] = 𝐩[j] ∘L 𝐩[i] := by
  rw [comp_eq_comp_add_commute, momentum_commutation_momentum, add_zero]

@[simp]
lemma momentumSqr_commutation_momentum : ⁅momentumOperatorSqr (d := d), 𝐩[i]⁆ = 0 := by
  simp [momentumOperatorSqr, sum_lie, leibniz_lie]

lemma momentumSqr_comp_momentum_commute : 𝐩² ∘L 𝐩[i] = 𝐩[i] ∘L 𝐩² := by
  rw [comp_eq_comp_add_commute, momentumSqr_commutation_momentum, add_zero]

/-
## Position / momentum commutators
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
  calc
    _ = 𝐱[i] (𝐩[j] ψ) x - 𝐩[j] (𝐱[i] ψ) x := by
      simp [bracket]
    _ = (I * ℏ) * (-x i * ∂[j] ψ x + ∂[j] (fun x ↦ x i * ψ x) x) := by
      simp only [positionOperator_apply_fun, momentumOperator_apply]
      ring
    _ = (I * ℏ) * (-x i * ∂[j] ψ x + ∂[j] ((fun x : Space d ↦ x i) • ⇑ψ) x) := rfl
    _ = (I * ℏ) * (∂[j] (fun x : Space d ↦ x i) x * ψ x) := by
      simp [Space.deriv_smul hdiff ψ.differentiableAt]
    _ = (I * ℏ) * δ[i,j] * ψ x := by
      rw [Space.deriv_component, ← kroneckerDelta, kroneckerDelta_symm]
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
  dsimp only [Bracket.bracket]
  ext ψ x
  simp only [coe_sub', coe_mul, Pi.sub_apply, Function.comp_apply, SchwartzMap.sub_apply, coe_smul',
    coe_comp', Pi.smul_apply, SchwartzMap.smul_apply, smul_eq_mul]
  simp only [momentumOperator_apply, positionOperator_apply, radiusRegPowOperator_apply_fun hε]

  have hne : ∀ x : Space d, ‖x‖ ^ 2 + ε ^ 2 ≠ 0 := by
    intro x
    apply ne_of_gt
    exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hε)

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

lemma momentum_comp_radiusRegPow_eq (hε : 0 < ε) (i : Fin d) :
    𝐩[i] ∘L 𝐫[ε,s] = 𝐫[ε,s] ∘L 𝐩[i] - (s * I * ℏ) • 𝐫[ε,s-2] ∘L 𝐱[i] := by
  rw [comp_eq_comp_sub_commute, radiusRegPow_commutation_momentum hε]

lemma radiusRegPow_commutation_momentumSqr (hε : 0 < ε) :
    ⁅radiusRegPowOperator (d := d) ε s, momentumOperatorSqr (d := d)⁆ =
    (2 * s * I * ℏ) • 𝐫[ε,s-2] ∘L ∑ i, 𝐱[i] ∘L 𝐩[i] + (s * (d + s - 2) * ℏ ^ 2) • 𝐫[ε,s-2]
    - (ε ^ 2 * s * (s - 2) * ℏ ^ 2) • 𝐫[ε,s-4] := by
  dsimp [momentumOperatorSqr]
  simp only [lie_sum, lie_leibniz, radiusRegPow_commutation_momentum hε, comp_smul, smul_comp,
    ← smul_add]
  conv_lhs =>
    enter [2, i]
    calc
      _ = (s * I * ℏ) • (𝐫[ε,s-2] ∘L 𝐱[i] ∘L 𝐩[i] + 𝐫[ε,s-2] ∘L 𝐩[i] ∘L 𝐱[i]
          - (↑(s - 2) * I * ℏ) • 𝐫[ε,s-4] ∘L 𝐱[i] ∘L 𝐱[i]) := by
        rw [add_comm, ← comp_assoc, momentum_comp_radiusRegPow_eq hε, comp_assoc, sub_comp, add_sub,
          smul_comp, comp_assoc, comp_assoc]
        ring_nf
      _ = (s * I * ℏ) • ((2 : ℂ) • 𝐫[ε,s-2] ∘L 𝐱[i] ∘L 𝐩[i] - (I * ℏ) • 𝐫[ε,s-2]
          - (↑(s - 2) * I * ℏ) • 𝐫[ε,s-4] ∘L 𝐱[i] ∘L 𝐱[i]) := by
        rw [momentum_comp_position_eq, comp_sub, comp_smul, add_sub, ← two_smul ℂ]
        simp [kroneckerDelta_self]
      _ = (2 * s * I * ℏ) • 𝐫[ε,s-2] ∘L 𝐱[i] ∘L 𝐩[i] + (s * ℏ ^ 2) • 𝐫[ε,s-2]
          + (s * (s - 2) * ℏ ^ 2) • 𝐫[ε,s-4] ∘L 𝐱[i] ∘L 𝐱[i] := by
        simp only [sub_eq_add_neg, ← neg_smul, smul_add, smul_smul]
        congr 3 -- match coefficients
        · ring
        · ring_nf
          simp
        · ring_nf
          simp only [I_sq, ofReal_add, ofReal_neg, RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe,
            MonoidHom.toOneHom_coe, MonoidHom.coe_coe, coe_algebraMap, ZeroHom.coe_mk, ofReal_mul,
            ofReal_pow]
          ring
  simp only [Finset.sum_add_distrib, ← Finset.smul_sum, ← comp_finset_sum]
  have h1 : (∑ i : Fin d, radiusRegPowOperator (d := d) ε (s - 2)) = (d : ℂ) • 𝐫[ε,s-2] := by
    ext
    rw [ContinuousLinearMap.sum_apply, SchwartzMap.sum_apply]
    simp
  have h2 : 𝐫[ε,s-4] ∘L ∑ i : Fin d, 𝐱[i] ∘L 𝐱[i] = 𝐫[ε,s-2] - (ε ^ 2) • 𝐫[ε,s-4] := by
    simp only [positionOperatorSqr_eq hε, comp_sub, comp_smul, comp_id,
      radiusRegPowOperator_comp_eq hε]
    ring_nf
  rw [h1, h2]
  ext ψ x
  simp only [ContinuousLinearMap.add_apply, coe_smul', Pi.smul_apply, coe_sub', Pi.sub_apply,
    SchwartzMap.add_apply, SchwartzMap.smul_apply, smul_eq_mul, real_smul, ofReal_mul,
    SchwartzMap.sub_apply, ofReal_sub, ofReal_add, ofReal_natCast]
  ring

/-
## Angular momentum / position commutators
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

/-
## Angular momentum / momentum commutators
-/

lemma angularMomentum_commutation_momentum {d : ℕ} (i j k : Fin d) : ⁅𝐋[i,j], 𝐩[k]⁆ =
    (Complex.I * ℏ * δ[i,k]) • 𝐩[j] - (Complex.I * ℏ * δ[j,k]) • 𝐩[i] := by
  unfold angularMomentumOperator
  rw [sub_lie]
  rw [leibniz_lie, leibniz_lie]
  rw [momentum_commutation_momentum, momentum_commutation_momentum]
  rw [position_commutation_momentum, position_commutation_momentum]
  simp only [ContinuousLinearMap.smul_comp, id_comp, comp_zero, zero_add]

lemma momentum_comp_angularMomentum_eq {d : ℕ} (i j k : Fin d) : 𝐩[k] ∘L 𝐋[i,j] =
    𝐋[i,j] ∘L 𝐩[k] - (Complex.I * ℏ * δ[i,k]) • 𝐩[j] + (Complex.I * ℏ * δ[j,k]) • 𝐩[i] := by
  rw [← sub_eq_zero, sub_add]
  rw [← angularMomentum_commutation_momentum]
  dsimp only [Bracket.bracket]
  simp only [ContinuousLinearMap.mul_def, sub_sub_cancel, sub_eq_zero]

lemma angularMomentum_commutation_momentumSqr {d : ℕ} (i j : Fin d) :
    ⁅𝐋[i,j], momentumOperatorSqr (d := d)⁆ = 0 := by
  unfold momentumOperatorSqr
  conv_lhs =>
    rw [lie_sum]
    enter [2, k]
    rw [lie_leibniz, angularMomentum_commutation_momentum]
    simp only [comp_sub, comp_smulₛₗ, RingHom.id_apply, sub_comp, smul_comp]
    rw [momentum_comp_commute _ i, momentum_comp_commute j _]
  dsimp only [kroneckerDelta]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_ite, mul_zero, ite_smul,
    zero_smul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, sub_self, add_zero]

lemma momentumSqr_comp_angularMomentum_commute {d : ℕ} (i j : Fin d) :
    𝐩² ∘L 𝐋[i,j] = 𝐋[i,j] ∘L 𝐩² := by
  apply Eq.symm
  rw [← sub_eq_zero]
  exact angularMomentum_commutation_momentumSqr i j

lemma angularMomentumSqr_commutation_momentumSqr {d : ℕ} :
    ⁅angularMomentumOperatorSqr (d := d), momentumOperatorSqr (d := d)⁆ = 0 := by
  unfold angularMomentumOperatorSqr
  simp only [smul_lie, sum_lie, leibniz_lie]
  simp [angularMomentum_commutation_momentumSqr]

/-
## Angular momentum / angular momentum commutators
-/

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
  simp only [mul_ite, mul_one, mul_zero, ite_smul, zero_smul, coe_sub', Pi.sub_apply,
    ContinuousLinearMap.add_apply, SchwartzMap.sub_apply, SchwartzMap.add_apply, smul_sub]
  ring

lemma angularMomentumSqr_commutation_angularMomentum {d : ℕ} (i j : Fin d) :
    ⁅angularMomentumOperatorSqr (d := d), 𝐋[i,j]⁆ = 0 := by
  unfold angularMomentumOperatorSqr
  conv_lhs =>
    simp only [smul_lie, sum_lie, leibniz_lie, angularMomentum_commutation_angularMomentum]
  dsimp only [kroneckerDelta]
  simp only [comp_add, comp_sub, add_comp, sub_comp, comp_smul, smul_comp, mul_ite, mul_zero,
    mul_one]
  simp only [ite_smul, zero_smul]

  -- Split into individual terms to do one of the sums, then recombine
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_irrel,
    Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]

  ext ψ x
  simp only [angularMomentumOperator_antisymm _ i, angularMomentumOperator_antisymm j _,
    neg_comp, comp_neg, neg_neg, smul_neg, sub_neg_eq_add]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.neg_apply, ContinuousLinearMap.zero_apply, SchwartzMap.add_apply,
    SchwartzMap.sum_apply, SchwartzMap.sub_apply, SchwartzMap.smul_apply, SchwartzMap.neg_apply,
    SchwartzMap.zero_apply]
  ring_nf
  rw [Finset.sum_const_zero, smul_zero]

end
end QuantumMechanics
