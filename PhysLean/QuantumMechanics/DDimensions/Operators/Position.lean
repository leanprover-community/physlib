/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import PhysLean.QuantumMechanics.DDimensions.Operators.Unbounded
public import PhysLean.QuantumMechanics.DDimensions.SpaceDHilbertSpace.SchwartzSubmodule
public import PhysLean.SpaceAndTime.Space.Derivatives.Basic
/-!

# Position operators

## i. Overview

In this module we introduce several position operators for quantum mechanics on `Space d`.

## ii. Key results

Definitions:
- `positionOperator` : (components of) the position vector operator acting on Schwartz maps
    `𝓢(Space d, ℂ)` by multiplication by `xᵢ`.
- `radiusRegPowOperator` : operator acting on Schwartz maps by multiplication by
    `(‖x‖² + ε²)^(s/2)`, a smooth regularization of `‖x‖ˢ`.
- `positionUnboundedOperator` : a symmetric unbounded operator acting on the Schwartz submodule
    of the Hilbert space `SpaceDHilbertSpace d`.
- `readiusRegPowUnboundedOperator` : a symmetric unbounded operator acting on the Schwartz
    submodule of the Hilbert space `SpaceDHilbertSpace d`. For `s ≤ 0` this operator is in fact
    bounded (by `|ε|ˢ`) and has natural domain the entire Hilbert space, but for uniformity we
    use the same domain for all `s`.

Notation:
- `𝐱[i]` for `positionOperator i`
- `𝐫[ε,s]` for `radiusRegPowOperator ε s`

## iii. Table of contents

- A. Position vector operator
- B. Regularized radius operator
- C. Unbounded position vector operator
- D. Unbounded regularized radius operator

## iv. References

-/

@[expose] public section

namespace QuantumMechanics
noncomputable section
open Space
open Function SchwartzMap ContDiff

variable {d : ℕ} (i : Fin d)

/-!

## A. Position vector operator

-/

/-- Component `i` of the position operator is the continuous linear map
  from `𝓢(Space d, ℂ)` to itself which maps `ψ` to `xᵢψ`. -/
def positionOperator : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (Complex.ofRealCLM ∘L coordCLM i)

@[inherit_doc positionOperator]
notation "𝐱[" i "]" => positionOperator i

lemma positionOperator_apply_fun (ψ : 𝓢(Space d, ℂ)) :
    𝐱[i] ψ = smulLeftCLM ℂ (coordCLM i) • ψ := by
  unfold positionOperator
  ext x
  simp [smulLeftCLM_apply_apply (g := Complex.ofRealCLM ∘ (coordCLM i)) (by fun_prop) _ _,
    smulLeftCLM_apply (g := coordCLM i) (by fun_prop) _]

@[simp]
lemma positionOperator_apply (ψ : 𝓢(Space d, ℂ)) (x : Space d) : 𝐱[i] ψ x = x i * ψ x := by
  simp [positionOperator_apply_fun, smulLeftCLM_apply (g := coordCLM i) (by fun_prop) _,
    coordCLM_apply, coord_apply]

/-!

## B. Regularized radius operator

-/
TODO "ZGCNP" "Incorporate normRegularizedPow into Space.Norm"

/-- Power of regularized norm, `(‖x‖² + ε²)^(s/2)`. -/
def normRegularizedPow (d : ℕ) (ε s : ℝ) : Space d → ℝ :=
  fun x ↦ (‖x‖ ^ 2 + ε ^ 2) ^ (s / 2)

lemma norm_sq_add_unit_sq_pos {d : ℕ} (ε : ℝˣ) (x : Space d) : 0 < ‖x‖ ^ 2 + ε ^ 2 :=
    Left.add_pos_of_nonneg_of_pos (sq_nonneg ‖x‖) (sq_pos_iff.mpr <| Units.ne_zero ε)

lemma normRegularizedPow_pos (d : ℕ) (ε : ℝˣ) (s : ℝ) (x : Space d) :
    0 < normRegularizedPow d ε s x :=
  Real.rpow_pos_of_pos (norm_sq_add_unit_sq_pos ε x) (s / 2)

lemma normRegularizedPow_hasTemperateGrowth (d : ℕ) (ε : ℝˣ) (s : ℝ) :
    HasTemperateGrowth (normRegularizedPow d ε s) := by
  -- Write `normRegularizedPow` as the composition of three simple functions
  -- to take advantage of `hasTemperateGrowth_one_add_norm_sq_rpow`.
  let f1 := fun (x : ℝ) ↦ (ε ^ 2) ^ (s / 2) * x
  let f2 := fun (x : Space d) ↦ (1 + ‖x‖ ^ 2) ^ (s / 2)
  let f3 := fun (x : Space d) ↦ ε.1⁻¹ • x
  have h123 : normRegularizedPow d ε s = f1 ∘ f2 ∘ f3 := by
    ext
    simp only [normRegularizedPow, f1, f2, f3, comp_apply, norm_smul, norm_inv, Real.norm_eq_abs]
    rw [← Real.mul_rpow (sq_nonneg ↑ε) (add_nonneg (zero_le_one' _) (sq_nonneg _))]
    simp [mul_add, mul_pow, add_comm]
  rw [h123]
  fun_prop

/-- The radius operator to power `s`, regularized by `ε ≠ 0`, is the continuous linear map
  from `𝓢(Space d, ℂ)` to itself which maps `ψ` to `(‖x‖² + ε²)^(s/2) • ψ`. -/
def radiusRegPowOperator {d : ℕ} (ε : ℝˣ) (s : ℝ) : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (Complex.ofReal ∘ normRegularizedPow d ε s)

@[inherit_doc radiusRegPowOperator]
notation "𝐫[" ε "," s "]" => radiusRegPowOperator ε s

@[inherit_doc radiusRegPowOperator]
notation "𝐫[" d "," ε "," s "]" => radiusRegPowOperator (d := d) ε s

lemma radiusRegPowOperator_apply_fun {d : ℕ} (ε : ℝˣ) (s : ℝ) (ψ : 𝓢(Space d, ℂ)) :
    𝐫[d,ε,s] ψ = fun x ↦ (‖x‖ ^ 2 + ε ^ 2) ^ (s / 2) • ψ x := by
  ext x
  dsimp [radiusRegPowOperator]
  refine smulLeftCLM_apply_apply ?_ ψ x
  exact HasTemperateGrowth.comp (by fun_prop) (normRegularizedPow_hasTemperateGrowth d ε s)

@[simp]
lemma radiusRegPowOperator_apply {d : ℕ} (ε : ℝˣ) (s : ℝ) (ψ : 𝓢(Space d, ℂ)) (x : Space d) :
    𝐫[ε,s] ψ x = (‖x‖ ^ 2 + ε ^ 2) ^ (s / 2) • ψ x := by
  rw [radiusRegPowOperator_apply_fun]

@[simp]
lemma radiusRegPowOperator_comp_eq {d : ℕ} (ε : ℝˣ) (s t : ℝ) :
    𝐫[d,ε,s] ∘L 𝐫[ε,t] = 𝐫[ε,s+t] := by
  ext ψ x
  simp [add_div, Real.rpow_add (norm_sq_add_unit_sq_pos ε x), mul_assoc]

@[simp]
lemma radiusRegPowOperator_zero {d : ℕ} (ε : ℝˣ) : 𝐫[d,ε,0] = 1 := by
  ext
  simp

lemma positionOperatorSqr_eq (d : ℕ) (ε : ℝˣ) : ∑ i, 𝐱[i] ∘L 𝐱[i] = 𝐫[d,ε,2] - ε.1 ^ 2 • 1 := by
  ext
  simp [Space.norm_sq_eq, add_mul, ← mul_assoc, ← pow_two, Finset.sum_mul]

/-!

## C. Unbounded position vector operator

-/

open SpaceDHilbertSpace

/-- The position operators defined on the Schwartz submodule. -/
def positionOperatorSchwartz : schwartzSubmodule d →ₗ[ℂ] schwartzSubmodule d :=
  schwartzEquiv.toLinearMap ∘ₗ 𝐱[i].toLinearMap ∘ₗ schwartzEquiv.symm.toLinearMap

lemma positionOperatorSchwartz_isSymmetric : (positionOperatorSchwartz i).IsSymmetric := by
  intro ψ ψ'
  obtain ⟨_, rfl⟩ := schwartzEquiv.surjective ψ
  obtain ⟨_, rfl⟩ := schwartzEquiv.surjective ψ'
  unfold positionOperatorSchwartz
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, comp_apply, schwartzEquiv_inner]
  congr with x
  simp only [LinearEquiv.symm_apply_apply, ContinuousLinearMap.coe_coe,
    positionOperator_apply, map_mul, Complex.conj_ofReal]
  ring

/-- The symmetric position unbounded operators with domain the Schwartz submodule
  of the Hilbert space. -/
def positionUnboundedOperator : UnboundedOperator (SpaceDHilbertSpace d) (SpaceDHilbertSpace d) :=
  UnboundedOperator.ofSymmetric (schwartzSubmodule_dense d) (positionOperatorSchwartz_isSymmetric i)

/-!

## D. Unbounded regularized radius operator

-/

/-- The (regularized) radius operators defined on the Schwartz submodule. -/
def radiusRegPowOperatorSchwartz {d : ℕ} (ε : ℝˣ) (s : ℝ) :
    schwartzSubmodule d →ₗ[ℂ] schwartzSubmodule d :=
  schwartzEquiv.toLinearMap ∘ₗ 𝐫[ε,s].toLinearMap ∘ₗ schwartzEquiv.symm.toLinearMap

lemma radiusRegPowOperatorSchwartz_isSymmetric {d : ℕ} (ε : ℝˣ) (s : ℝ) :
    (radiusRegPowOperatorSchwartz (d := d) ε s).IsSymmetric := by
  intro ψ ψ'
  obtain ⟨_, rfl⟩ := schwartzEquiv.surjective ψ
  obtain ⟨_, rfl⟩ := schwartzEquiv.surjective ψ'
  simp only [radiusRegPowOperatorSchwartz, LinearMap.coe_comp, LinearEquiv.coe_coe, comp_apply,
    schwartzEquiv_inner]
  congr with x -- match integrands
  simp only [LinearEquiv.symm_apply_apply, ContinuousLinearMap.coe_coe, radiusRegPowOperator_apply,
    Complex.real_smul, map_mul, Complex.conj_ofReal]
  ring

/-- The symmetric (regularized) radius unbounded operators with domain the Schwartz submodule
  of the Hilbert space. -/
def radiusRegPowUnboundedOperator {d : ℕ} (ε : ℝˣ) (s : ℝ) :
    UnboundedOperator (SpaceDHilbertSpace d) (SpaceDHilbertSpace d) :=
  UnboundedOperator.ofSymmetric (schwartzSubmodule_dense d)
    (radiusRegPowOperatorSchwartz_isSymmetric ε s)

end
end QuantumMechanics
