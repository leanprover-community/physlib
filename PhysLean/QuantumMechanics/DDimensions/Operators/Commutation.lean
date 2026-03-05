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
open Constants
open KroneckerDelta
open SchwartzMap ContinuousLinearMap

private lemma ite_cond_symm (i j : Fin d) :
    (if i = j then A else B) = (if j = i then A else B) :=
  ite_cond_congr (Eq.propIntro Eq.symm Eq.symm)

lemma leibniz_lie {d : ℕ} (A B C : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ)) :
    ⁅A ∘L B, C⁆ = A ∘L ⁅B, C⁆ + ⁅A, C⁆ ∘L B := by
  dsimp only [Bracket.bracket]
  simp only [ContinuousLinearMap.mul_def, comp_assoc, comp_sub, sub_comp, sub_add_sub_cancel]

lemma lie_leibniz {d : ℕ} (A B C : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ)) :
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

/-
## Position / position commutators
-/

/-- Position operators commute: `[xᵢ, xⱼ] = 0`. -/
lemma position_commutation_position {d : ℕ} (i j : Fin d) : ⁅𝐱[i], 𝐱[j]⁆ = 0 := by
  dsimp only [Bracket.bracket]
  ext ψ x
  simp only [coe_sub', coe_mul, Pi.sub_apply, Function.comp_apply, SchwartzMap.sub_apply,
    ContinuousLinearMap.zero_apply, SchwartzMap.zero_apply, positionOperator_apply]
  ring

lemma position_comp_commute {d : ℕ} (i j : Fin d) : 𝐱[i] ∘L 𝐱[j] = 𝐱[j] ∘L 𝐱[i] := by
  rw [← sub_eq_zero]
  exact position_commutation_position i j

lemma position_commutation_radiusRegPow (hε : 0 < ε) (i : Fin d) :
    ⁅𝐱[i], radiusRegPowOperator (d := d) ε s⁆ = 0 := by
  dsimp only [Bracket.bracket]
  ext ψ x
  simp only [coe_sub', coe_mul, Pi.sub_apply, Function.comp_apply, SchwartzMap.sub_apply]
  simp only [positionOperator_apply, radiusRegPowOperator_apply hε]
  simp only [Complex.real_smul, ContinuousLinearMap.zero_apply, SchwartzMap.zero_apply]
  ring

lemma position_comp_radiusRegPow_commute (hε : 0 < ε) (i : Fin d) :
    𝐱[i] ∘L 𝐫[ε,s] = 𝐫[ε,s] ∘L 𝐱[i] := by
  rw [← sub_eq_zero]
  exact position_commutation_radiusRegPow hε _

lemma radiusRegPow_commutation_radiusRegPow (hε : 0 < ε) :
    ⁅radiusRegPowOperator (d := d) ε s, radiusRegPowOperator (d := d) ε t⁆ = 0 := by
  dsimp only [Bracket.bracket]
  simp only [ContinuousLinearMap.mul_def, radiusRegPowOperator_comp_eq hε, add_comm, sub_self]

/-
## Momentum / momentum commutators
-/

/-- Momentum operators commute: `[pᵢ, pⱼ] = 0`. -/
lemma momentum_commutation_momentum {d : ℕ} (i j : Fin d) : ⁅𝐩[i], 𝐩[j]⁆ = 0 := by
  dsimp only [Bracket.bracket]
  ext ψ x
  simp only [coe_sub', coe_mul, Pi.sub_apply, Function.comp_apply, SchwartzMap.sub_apply,
    ContinuousLinearMap.zero_apply, SchwartzMap.zero_apply, momentumOperator_apply_fun]
  rw [Space.deriv_const_smul _ ?_, Space.deriv_const_smul _ ?_]
  · rw [Space.deriv_commute _ (ψ.smooth _), sub_self]
  · exact Space.deriv_differentiable (ψ.smooth _) i
  · exact Space.deriv_differentiable (ψ.smooth _) j

lemma momentum_comp_commute {d : ℕ} (i j : Fin d) : 𝐩[i] ∘L 𝐩[j] = 𝐩[j] ∘L 𝐩[i] := by
  rw [← sub_eq_zero]
  exact momentum_commutation_momentum i j

lemma momentumSqr_commutation_momentum {d : ℕ} (i : Fin d) :
    ⁅momentumOperatorSqr (d := d), 𝐩[i]⁆ = 0 := by
  dsimp only [Bracket.bracket, momentumOperatorSqr]
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  conv_lhs =>
    enter [2, j]
    simp only [ContinuousLinearMap.mul_def]
    rw [comp_assoc]
    rw [momentum_comp_commute j i, ← comp_assoc]
    rw [momentum_comp_commute j i, comp_assoc]
    rw [sub_self]
  rw [Finset.sum_const_zero]

lemma momentumSqr_comp_momentum_commute {d : ℕ} (i : Fin d) : 𝐩² ∘L 𝐩[i] = 𝐩[i] ∘L 𝐩² := by
  rw [← sub_eq_zero]
  exact momentumSqr_commutation_momentum i

/-
## Position / momentum commutators
-/

/-- The canonical commutation relations: `[xᵢ, pⱼ] = iℏ δᵢⱼ𝟙`. -/
lemma position_commutation_momentum {d : ℕ} (i j : Fin d) : ⁅𝐱[i], 𝐩[j]⁆ =
    (Complex.I * ℏ * δ[i,j]) • ContinuousLinearMap.id ℂ 𝓢(Space d, ℂ) := by
  dsimp only [Bracket.bracket, kroneckerDelta]
  ext ψ x
  simp only [ContinuousLinearMap.smul_apply, SchwartzMap.smul_apply, coe_id', id_eq, smul_eq_mul,
    coe_sub', coe_mul, Pi.sub_apply, Function.comp_apply, SchwartzMap.sub_apply]
  rw [positionOperator_apply, momentumOperator_apply_fun]
  rw [momentumOperator_apply, positionOperator_apply_fun]
  simp only [neg_mul, Pi.smul_apply, smul_eq_mul, mul_neg, sub_neg_eq_add]
  have h : ⇑(smulLeftCLM ℂ ⇑(Space.coordCLM i) • ψ) = (fun (x : Space d) ↦ x i) • ψ := by
    ext x
    rw [ContinuousLinearMap.smul_def, smulLeftCLM_apply_apply (by fun_prop), Space.coordCLM_apply]
    simp only [Space.coord_apply, Complex.real_smul, Pi.smul_apply']
  rw [h]
  rw [Space.deriv_smul (by fun_prop) (SchwartzMap.differentiableAt ψ)]
  rw [Space.deriv_component, ite_cond_symm j i]
  simp only [mul_add, Complex.real_smul, ite_smul, one_smul, zero_smul, mul_ite, mul_one, mul_zero,
    ite_mul, zero_mul]
  ring

lemma momentum_comp_position_eq (i j : Fin d) : 𝐩[j] ∘L 𝐱[i] =
    𝐱[i] ∘L 𝐩[j] - (Complex.I * ℏ * δ[i,j]) • ContinuousLinearMap.id ℂ 𝓢(Space d, ℂ) := by
  rw [← position_commutation_momentum]
  dsimp only [Bracket.bracket]
  simp only [ContinuousLinearMap.mul_def, sub_sub_cancel]

lemma position_position_commutation_momentum {d : ℕ} (i j k : Fin d) : ⁅𝐱[i] ∘L 𝐱[j], 𝐩[k]⁆ =
    (Complex.I * ℏ * δ[i,k]) • 𝐱[j] + (Complex.I * ℏ * δ[j,k]) • 𝐱[i] := by
  rw [leibniz_lie]
  rw [position_commutation_momentum, position_commutation_momentum]
  rw [ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp]
  rw [id_comp, comp_id]
  rw [add_comm]

lemma position_commutation_momentum_momentum {d : ℕ} (i j k : Fin d) : ⁅𝐱[i], 𝐩[j] ∘L 𝐩[k]⁆ =
    (Complex.I * ℏ * δ[i,k]) • 𝐩[j] + (Complex.I * ℏ * δ[i,j]) • 𝐩[k] := by
  rw [lie_leibniz]
  rw [position_commutation_momentum, position_commutation_momentum]
  rw [ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp]
  rw [id_comp, comp_id]

lemma position_commutation_momentumSqr {d : ℕ} (i : Fin d) : ⁅𝐱[i], 𝐩²⁆ =
    (2 * Complex.I * ℏ) • 𝐩[i] := by
  unfold momentumOperatorSqr
  rw [lie_sum]
  simp only [position_commutation_momentum_momentum]
  dsimp only [kroneckerDelta]
  simp only [mul_ite_zero, ite_zero_smul, Finset.sum_add_distrib, Finset.sum_ite_eq,
    Finset.mem_univ, ↓reduceIte]
  ext ψ x
  simp only [ContinuousLinearMap.add_apply, coe_smul', Pi.smul_apply, SchwartzMap.add_apply,
    SchwartzMap.smul_apply, smul_eq_mul]
  ring

lemma radiusRegPow_commutation_momentum (hε : 0 < ε) (i : Fin d) :
    ⁅radiusRegPowOperator (d := d) ε s, 𝐩[i]⁆ = (s * Complex.I * ℏ) • 𝐫[ε,s-2] ∘L 𝐱[i] := by
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
    𝐩[i] ∘L 𝐫[ε,s] = 𝐫[ε,s] ∘L 𝐩[i] - (s * Complex.I * ℏ) • 𝐫[ε,s-2] ∘L 𝐱[i] := by
  rw [← radiusRegPow_commutation_momentum hε]
  dsimp only [Bracket.bracket]
  simp only [ContinuousLinearMap.mul_def, sub_sub_cancel]

lemma radiusRegPow_commutation_momentumSqr (hε : 0 < ε) :
    ⁅radiusRegPowOperator (d := d) ε s, momentumOperatorSqr (d := d)⁆ =
    (2 * s * Complex.I * ℏ) • 𝐫[ε,s-2] ∘L ∑ i, 𝐱[i] ∘L 𝐩[i]
    + (s * ℏ ^ 2) • ((d + s - 2) • 𝐫[ε,s-2] - (ε ^ 2 * (s - 2)) • 𝐫[ε,s-4]) := by
  unfold momentumOperatorSqr
  rw [lie_sum]
  conv_lhs =>
    enter [2, i]
    rw [lie_leibniz, radiusRegPow_commutation_momentum hε]
    rw [comp_smul, ← comp_assoc, momentum_comp_radiusRegPow_eq hε]
    rw [sub_comp, comp_assoc, momentum_comp_position_eq]
    simp only [kroneckerDelta, ↓reduceIte, mul_one]
  simp only [smul_comp, comp_sub, comp_smul, comp_id, smul_sub, comp_assoc,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.smul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, ← ContinuousLinearMap.comp_finset_sum]
  rw [positionOperatorSqr_eq hε, comp_sub, radiusRegPowOperator_comp_eq hε, comp_smul, comp_id]
  rw [← Nat.cast_smul_eq_nsmul ℂ]
  ext ψ x
  simp only [Complex.ofReal_sub, Complex.ofReal_ofNat, sub_add_cancel, coe_sub', Pi.sub_apply,
    ContinuousLinearMap.add_apply, coe_smul', coe_comp', coe_sum', Pi.smul_apply,
    Function.comp_apply, Finset.sum_apply, map_sum, SchwartzMap.sub_apply, SchwartzMap.add_apply,
    SchwartzMap.smul_apply, SchwartzMap.sum_apply, smul_eq_mul, Complex.real_smul,
    Complex.ofReal_pow, Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_mul]
  ring_nf
  rw [Complex.I_sq]
  ring

/-
## Angular momentum / position commutators
-/

lemma angularMomentum_commutation_position {d : ℕ} (i j k : Fin d) : ⁅𝐋[i,j], 𝐱[k]⁆ =
    (Complex.I * ℏ * δ[i,k]) • 𝐱[j] - (Complex.I * ℏ * δ[j,k]) • 𝐱[i] := by
  unfold angularMomentumOperator
  rw [sub_lie]
  rw [leibniz_lie, leibniz_lie]
  rw [position_commutation_position, position_commutation_position]
  rw [← lie_skew, position_commutation_momentum]
  rw [← lie_skew, position_commutation_momentum]
  rw [kroneckerDelta_symm k i, kroneckerDelta_symm k j]
  simp only [ContinuousLinearMap.comp_neg, ContinuousLinearMap.comp_smul, comp_id, zero_comp,
    add_zero, add_comm, sub_neg_eq_add, ← sub_eq_add_neg]

lemma angularMomentum_commutation_radiusRegPow (hε : 0 < ε) (i j : Fin d) :
    ⁅𝐋[i,j], radiusRegPowOperator (d := d) ε s⁆ = 0 := by
  dsimp only [Bracket.bracket]
  unfold angularMomentumOperator
  simp only [sub_mul, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc]
  repeat rw [momentum_comp_radiusRegPow_eq hε]
  simp only [comp_sub, comp_smulₛₗ, RingHom.id_apply, ← ContinuousLinearMap.comp_assoc]
  repeat rw [position_comp_radiusRegPow_commute hε]
  simp only [ContinuousLinearMap.comp_assoc]
  rw [position_comp_commute]
  simp only [sub_sub_sub_cancel_right, sub_self]

lemma angularMomentumSqr_commutation_radiusRegPow (hε : 0 < ε) :
    ⁅angularMomentumOperatorSqr (d := d), radiusRegPowOperator (d := d) ε s⁆ = 0 := by
  unfold angularMomentumOperatorSqr
  simp only [sum_lie, smul_lie, leibniz_lie, angularMomentum_commutation_radiusRegPow hε,
    comp_zero, zero_comp, add_zero, smul_zero, Finset.sum_const_zero]

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
