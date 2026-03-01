/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
import PhysLean.SpaceAndTime.Space.Derivatives.Basic
/-!

# Position operators

In this module we define:
- The position vector operator on Schwartz maps, component-wise.
- The (regularized) real powers of the radius operator on Schwartz maps.

-/

namespace QuantumMechanics
noncomputable section
open Space
open Function SchwartzMap ContDiff

/-
## Position vector operator
-/

/-- Component `i` of the position operator is the continuous linear map
from `𝓢(Space d, ℂ)` to itself which maps `ψ` to `xᵢψ`. -/
def positionOperator (i : Fin d) : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (Complex.ofReal ∘ coordCLM i)

@[inherit_doc positionOperator]
macro "𝐱[" i:term "]" : term => `(positionOperator $i)

lemma positionOperator_apply_fun (i : Fin d) (ψ : 𝓢(Space d, ℂ)) :
    𝐱[i] ψ = (fun x ↦ x i * ψ x) := by
  unfold positionOperator
  ext x
  rw [SchwartzMap.smulLeftCLM_apply_apply]
  · rw [Function.comp_apply, smul_eq_mul]
    rw [coordCLM_apply, coord_apply]
  · fun_prop

lemma positionOperator_apply (i : Fin d) (ψ : 𝓢(Space d, ℂ)) (x : Space d) :
    𝐱[i] ψ x = x i * ψ x := by rw [positionOperator_apply_fun]

/-

## Radius operator

-/
TODO "ZGCNP" "Incorporate normRegularizedPow into Space.Norm"

/-- Power of regularized norm, `(‖x‖² + ε²)^(s/2)` -/
private def normRegularizedPow (ε s : ℝ) : Space d → ℝ :=
  fun x ↦ (‖x‖ ^ 2 + ε ^ 2) ^ (s / 2)

private lemma normRegularizedPow_hasTemperateGrowth (hε : 0 < ε) :
    HasTemperateGrowth (normRegularizedPow (d := d) ε s) := by
  -- Write `normRegularizedPow` as the composition of three simple functions
  -- to take advantage of `hasTemperateGrowth_one_add_norm_sq_rpow`
  let f1 := fun (x : ℝ) ↦ (ε ^ 2) ^ (s / 2) * x
  let f2 := fun (x : Space d) ↦ (1 + ‖x‖ ^ 2) ^ (s / 2)
  let f3 := fun (x : Space d) ↦ ε⁻¹ • x

  have h123 : normRegularizedPow (d := d) ε s = f1 ∘ f2 ∘ f3 := by
    unfold normRegularizedPow f1 f2 f3
    ext x
    simp only [Function.comp_apply, norm_smul, norm_inv, Real.norm_eq_abs]
    rw [← Real.mul_rpow (sq_nonneg _) ?_]
    · rw [mul_pow, mul_add, mul_one, ← mul_assoc, inv_pow, sq_abs]
      rw [IsUnit.mul_inv_cancel ?_]
      · rw [one_mul, add_comm]
      · rw [pow_two, isUnit_mul_self_iff, isUnit_iff_ne_zero]
        exact ne_of_gt hε
    · exact add_nonneg (zero_le_one' _) (sq_nonneg _)

  rw [h123]
  fun_prop

/-- The radius operator to power `s`, regularized by `ε ≠ 0`, is the continuous linear map
  from `𝓢(Space d, ℂ)` to itself which maps `ψ` to `(‖x‖² + ε²)^(s/2) • ψ`. -/
def radiusRegPowOperator (ε s : ℝ) : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (Complex.ofReal ∘ normRegularizedPow ε s)

@[inherit_doc radiusRegPowOperator]
macro "𝐫[" ε:term "," s:term "]" : term => `(radiusRegPowOperator $ε $s)

lemma radiusRegPowOperator_apply_fun (hε : 0 < ε) :
    𝐫[ε,s] ψ = fun x ↦ (‖x‖ ^ 2 + ε ^ 2) ^ (s / 2) • ψ x := by
  unfold radiusRegPowOperator
  ext x
  rw [smulLeftCLM_apply_apply]
  · unfold normRegularizedPow
    rw [comp_apply, smul_eq_mul, Complex.real_smul]
  · exact HasTemperateGrowth.comp (by fun_prop) (normRegularizedPow_hasTemperateGrowth hε)

lemma radiusRegPowOperator_apply (hε : 0 < ε) :
    𝐫[ε,s] ψ x = (‖x‖ ^ 2 + ε ^ 2) ^ (s / 2) • ψ x := by
  rw [radiusRegPowOperator_apply_fun hε]

lemma radiusRegPowOperator_comp_eq (hε : 0 < ε) (s t : ℝ) :
    (radiusRegPowOperator (d := d) ε s) ∘L 𝐫[ε,t] = 𝐫[ε,s+t] := by
  unfold radiusRegPowOperator
  ext ψ x
  simp only [ContinuousLinearMap.coe_comp', comp_apply]
  repeat rw [smulLeftCLM_apply_apply ?_]
  · unfold normRegularizedPow
    simp only [comp_apply, smul_eq_mul]
    rw [← mul_assoc, ← Complex.ofReal_mul]
    rw [← Real.rpow_add]
    · congr
      ring
    · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hε)
  repeat exact HasTemperateGrowth.comp (by fun_prop) (normRegularizedPow_hasTemperateGrowth hε)

lemma radiusRegPowOperator_zero (hε : 0 < ε) :
    𝐫[ε,0] = ContinuousLinearMap.id ℂ 𝓢(Space d, ℂ) := by
  ext ψ x
  rw [radiusRegPowOperator_apply hε, zero_div, Real.rpow_zero, one_smul,
    ContinuousLinearMap.coe_id', id_eq]

lemma positionOperatorSqr_eq (hε : 0 < ε) : ∑ i, 𝐱[i] ∘L 𝐱[i] =
    𝐫[ε,2] - ε ^ 2 • ContinuousLinearMap.id ℂ 𝓢(Space d, ℂ) := by
  ext ψ x
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, SchwartzMap.sum_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply, SchwartzMap.sub_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, SchwartzMap.smul_apply]
  simp only [positionOperator_apply_fun, radiusRegPowOperator_apply_fun hε]
  simp only [← mul_assoc, ← Finset.sum_mul, ← Complex.ofReal_mul]
  rw [div_self (by norm_num), Real.rpow_one, ← sub_smul, add_sub_cancel_right]
  rw [Space.norm_sq_eq, Complex.real_smul, Complex.ofReal_sum]
  simp only [pow_two]

end
end QuantumMechanics
