/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhi Kai Pong, Joseph Tooby-Smith, Lode Vermeulen
-/
import PhysLean.SpaceAndTime.Space.Derivatives.Basic
/-!

# Gradient of functions and distributions on `Space d`

## i. Overview

This module defines and proves basic properties of the gradient operator
on functions from `Space d` to `ℝ` and on distributions from `Space d` to `ℝ`.

The gradient operator returns a vector field whose components are the partial derivatives
of the input function with respect to each spatial coordinate.

## ii. Key results

- `grad` : The gradient operator on functions from `Space d` to `ℝ`.
- `distGrad` : The gradient operator on distributions from `Space d` to `ℝ`.

## iii. Table of contents

- A. The gradient of functions on `Space d`
  - A.1. Gradient of the zero function
  - A.2. Gradient distributes over addition
  - A.3. Gradient of a constant function
  - A.4. Gradient distributes over scalar multiplication
  - A.5. Gradient distributes over negation
  - A.6. Expansion in terms of basis vectors
  - A.7. Components of the gradient
  - A.8. Inner product with a gradient
  - A.9. Gradient is equal to `gradient` from Mathlib
  - A.10. Value of gradient in the direction of the position vector
  - A.11. Gradient of the norm squared function
  - A.12. Gradient of the inner product function
  - A.13. Integrability with bounded functions
- B. Gradient of distributions
  - B.1. The definition
  - B.2. The gradient of inner products
  - B.3. The gradient as a sum over basis vectors
  - B.4. The underlying function of the gradient distribution
  - B.5. The gradient applied to a Schwartz function

## iv. References

-/

namespace Space

/-!

## A. The gradient of functions on `Space d`

-/

/-- The vector calculus operator `grad`. -/
noncomputable def grad {d} (f : Space d → ℝ) :
  Space d → EuclideanSpace ℝ (Fin d) := fun x => WithLp.toLp 2 fun i => ∂[i] f x

@[inherit_doc grad]
scoped[Space] notation "∇" => grad

/-!

### A.1. Gradient of the zero function

-/

@[simp]
lemma grad_zero : ∇ (0 : Space d → ℝ) = 0 := by
  unfold grad Space.deriv
  simp only [fderiv_zero, Pi.zero_apply, ContinuousLinearMap.zero_apply]
  rfl

/-!

### A.2. Gradient distributes over addition

-/

lemma grad_add (f1 f2 : Space d → ℝ)
    (hf1 : Differentiable ℝ f1) (hf2 : Differentiable ℝ f2) :
    ∇ (f1 + f2) = ∇ f1 + ∇ f2 := by
  unfold grad
  ext x i
  simp only [Pi.add_apply]
  rw [deriv_add]
  rfl
  exact hf1
  exact hf2

/-!

### A.3. Gradient of a constant function

-/

@[simp]
lemma grad_const : ∇ (fun _ : Space d => c) = 0 := by
  unfold grad Space.deriv
  simp only [fderiv_fun_const, Pi.ofNat_apply, ContinuousLinearMap.zero_apply]
  rfl

/-!

### A.4. Gradient distributes over scalar multiplication

-/

lemma grad_smul (f : Space d → ℝ) (k : ℝ)
    (hf : Differentiable ℝ f) :
    ∇ (k • f) = k • ∇ f := by
  unfold grad
  ext x i
  simp only [Pi.smul_apply]
  rw [deriv_const_smul]
  rfl
  exact hf

/-!

### A.5. Gradient distributes over negation

-/

lemma grad_neg (f : Space d → ℝ) :
    ∇ (- f) = - ∇ f := by
  unfold grad
  ext x i
  simp only [Pi.neg_apply]
  rw [Space.deriv_eq, fderiv_neg]
  rfl

/-!

### A.6. Expansion in terms of basis vectors

-/

lemma grad_eq_sum {d} (f : Space d → ℝ) (x : Space d) :
    ∇ f x = ∑ i, deriv i f x • EuclideanSpace.single i 1 := by
  ext i
  simp [grad, deriv_eq, - WithLp.ofLp_sum]
  trans ∑ x_1, (fderiv ℝ f x) (basis x_1) • (EuclideanSpace.single x_1 1).ofLp i; swap
  · change _ = WithLp.linearEquiv 2 ℝ (V := Fin d → ℝ) (∑ x_1, (fderiv ℝ f x) (basis x_1) •
      EuclideanSpace.single x_1 1) i
    rw [map_sum, Finset.sum_apply]
    rfl
  rw [Finset.sum_eq_single i]
  · simp [basis]
  · intro j hj
    simp [basis]
    exact fun a a_1 => False.elim (a (id (Eq.symm a_1)))
  · simp

/-!

### A.7. Components of the gradient

-/

lemma grad_apply {d} (f : Space d → ℝ) (x : Space d) (i : Fin d) :
    (∇ f x) i = deriv i f x := by
  rw [grad_eq_sum]
  change WithLp.linearEquiv 2 ℝ (Fin d → ℝ) (∑ x_1, (fderiv ℝ f x) (basis x_1) •
    EuclideanSpace.single x_1 1) i = _
  rw [map_sum, Finset.sum_apply]
  simp [Pi.single_apply]
  rfl

/-!

### A.8. Inner product with a gradient

-/

open InnerProductSpace

lemma grad_inner_single {d} (f : Space d → ℝ) (x : Space d) (i : Fin d) :
    ⟪∇ f x, EuclideanSpace.single i 1⟫_ℝ = deriv i f x := by
  simp only [EuclideanSpace.inner_single_right, conj_trivial,
    one_mul]
  exact rfl

lemma grad_inner_eq {d} (f : Space d → ℝ) (x : Space d) (y : EuclideanSpace ℝ (Fin d)) :
    ⟪∇ f x, y⟫_ℝ = ∑ i, y i * ∂[i] f x:= by
  have hy : y = ∑ i, y i • EuclideanSpace.basisFun (Fin d) ℝ i := by
      conv_lhs => rw [← OrthonormalBasis.sum_repr (EuclideanSpace.basisFun (Fin d) ℝ) y]
      dsimp [basis]
  conv_lhs => rw [hy, inner_sum]
  simp [inner_smul_right, grad_inner_single]

lemma inner_grad_eq {d} (f : Space d → ℝ) (x : EuclideanSpace ℝ (Fin d)) (y : Space d) :
    ⟪x, ∇ f y⟫_ℝ = ∑ i, x i * ∂[i] f y := by
  rw [← grad_inner_eq]
  exact real_inner_comm (∇ f y) x

lemma grad_inner_repr_eq {d} (f : Space d → ℝ) (x y : Space d) :
    ⟪∇ f x, (Space.basis).repr y⟫_ℝ = fderiv ℝ f x y := by
  rw [grad_inner_eq f x ((Space.basis).repr y), Space.fderiv_eq_sum_deriv]
  simp

lemma repr_grad_inner_eq {d} (f : Space d → ℝ) (x y : Space d) :
    ⟪(Space.basis).repr x, ∇ f y⟫_ℝ = fderiv ℝ f y x := by
  rw [← grad_inner_repr_eq f y x]
  exact real_inner_comm (∇ f y) ((Space.basis).repr x)

/-!

### A.9. Gradient is equal to `gradient` from Mathlib

-/

lemma grad_eq_gradiant {d} (f : Space d → ℝ) :
    ∇ f = basis.repr ∘ gradient f := by
  funext x
  have hx (y : EuclideanSpace ℝ (Fin d)) : ⟪(Space.basis).repr (gradient f x), y⟫_ℝ =
      ⟪∇ f x, y⟫_ℝ := by
    rw [gradient, basis_repr_inner_eq, toDual_symm_apply]
    simp [grad_inner_eq f x, fderiv_eq_sum_deriv]
  have h1 : ∀ y, ⟪(Space.basis).repr (gradient f x) - ∇ f x, y⟫_ℝ = 0 := by
    intro y
    rw [inner_sub_left, hx y]
    simp
  have h2 := h1 (basis.repr (gradient f x) - ∇ f x)
  rw [inner_self_eq_zero, sub_eq_zero] at h2
  simp [h2]

lemma gradient_eq_grad {d} (f : Space d → ℝ) :
    gradient f = basis.repr.symm ∘ ∇ f := by
  rw [grad_eq_gradiant f]
  ext x
  simp

lemma gradient_eq_sum {d} (f : Space d → ℝ) (x : Space d) :
    gradient f x = ∑ i, deriv i f x • basis i := by
  simp [gradient_eq_grad, grad_eq_sum f x]

lemma euclid_gradient_eq_sum {d} (f : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    gradient f x = ∑ i, fderiv ℝ f x (EuclideanSpace.single i 1) • EuclideanSpace.single i 1 := by
  apply ext_inner_right (𝕜 := ℝ) fun y => ?_
  simp [gradient]
  have hy : y = ∑ i, y i • EuclideanSpace.single i 1 := by
    conv_lhs => rw [← OrthonormalBasis.sum_repr (EuclideanSpace.basisFun (Fin d) ℝ) y]
    simp
  conv_lhs => rw [hy]
  simp [sum_inner, inner_smul_left, EuclideanSpace.inner_single_left]
  congr
  funext i
  ring

/-!

### A.10. Value of gradient in the direction of the position vector

-/

/-- The gradient in the direction of the space position. -/
lemma grad_inner_space_unit_vector {d} (x : Space d) (f : Space d → ℝ) (hd : Differentiable ℝ f) :
    ⟪∇ f x, ‖x‖⁻¹ • basis.repr x⟫_ℝ = _root_.deriv (fun r => f (r • ‖x‖⁻¹ • x)) ‖x‖ := by
  by_cases hx : x = 0
  · subst hx
    simp
  symm
  calc _
    _ = fderiv ℝ (f ∘ (fun r => r • ‖x‖⁻¹ • x)) ‖x‖ 1 := by rfl
    _ = (fderiv ℝ f (‖x‖ • ‖x‖⁻¹ • x)) (_root_.deriv (fun r => r • ‖x‖⁻¹ • x) ‖x‖) := by
      rw [fderiv_comp _ (by fun_prop) (by fun_prop)]
      simp
    _ = (fderiv ℝ f x) (_root_.deriv (fun r => r • ‖x‖⁻¹ • x) ‖x‖) := by
      have hx : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
      rw [smul_smul]
      field_simp
      simp
  rw [grad_inner_eq f x (‖x‖⁻¹ • basis.repr x)]
  rw [deriv_smul_const (by fun_prop)]
  simp only [deriv_id'', one_smul, map_smul, fderiv_eq_sum_deriv, smul_eq_mul, Finset.mul_sum,
    PiLp.smul_apply, basis_repr_apply]
  ring_nf

lemma grad_inner_space {d} (x : Space d) (f : Space d → ℝ) (hd : Differentiable ℝ f) :
    ⟪∇ f x, basis.repr x⟫_ℝ = ‖x‖ * _root_.deriv (fun r => f (r • ‖x‖⁻¹ • x)) ‖x‖ := by
  rw [← grad_inner_space_unit_vector _ _ hd, inner_smul_right]
  by_cases hx : x = 0
  · subst hx
    simp
  have hx : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  field_simp

/-!

### A.11. Gradient of the norm squared function

-/

lemma grad_norm_sq (x : Space d) :
    ∇ (fun x => ‖x‖ ^ 2) x = (2 : ℝ) • basis.repr x := by
  ext i
  rw [grad_eq_sum]
  change WithLp.linearEquiv 2 ℝ (Fin d → ℝ) (∑ x_1, (fderiv ℝ (fun x => ‖x‖ ^ 2) x) (basis x_1) •
    EuclideanSpace.single x_1 1) i = _
  rw [map_sum, Finset.sum_apply]
  simp [Pi.single_apply]

/-!

### A.12. Gradient of the inner product function

-/

/-- The gradient of the inner product is given by `2 • x`. -/
lemma grad_inner {d : ℕ} :
    ∇ (fun y : Space d => ⟪y, y⟫_ℝ) = fun z => (2 : ℝ) • basis.repr z := by
  ext z i
  simp [Space.grad]
  rw [deriv]
  simp only [fderiv_norm_sq_apply, ContinuousLinearMap.coe_smul', coe_innerSL_apply, Pi.smul_apply,
    nsmul_eq_mul, Nat.cast_ofNat, mul_eq_mul_left_iff, OfNat.ofNat_ne_zero, or_false]
  simp

lemma grad_inner_left {d : ℕ} (x : Space d) :
    ∇ (fun y : Space d => ⟪y, x⟫_ℝ) = fun _ => basis.repr x := by
  ext z i
  simp [Space.grad]

lemma grad_inner_right {d : ℕ} (x : Space d) :
    ∇ (fun y : Space d => ⟪x, y⟫_ℝ) = fun _ => basis.repr x := by
  rw [← grad_inner_left x]
  congr
  funext y
  exact real_inner_comm y x

/-!

### A.13. Integrability with bounded functions

-/

open InnerProductSpace Distribution SchwartzMap MeasureTheory

/- The quantity `⟪f x, Space.grad η x⟫_ℝ` is integrable for `f` bounded
  and `η` a Schwartz map. -/
lemma integrable_isDistBounded_inner_grad_schwartzMap {dm1 : ℕ}
    {f : Space dm1.succ → EuclideanSpace ℝ (Fin dm1.succ)}
    (hf : IsDistBounded f) (η : 𝓢(Space dm1.succ, ℝ)) :
    Integrable (fun x => ⟪f x, Space.grad η x⟫_ℝ) volume := by
  conv =>
    enter [1, x]
    rw [grad_eq_sum, inner_sum]
  apply MeasureTheory.integrable_finset_sum
  intro i _
  simp [inner_smul_right]
  have integrable_lemma (i j : Fin (dm1 + 1)) :
      Integrable (fun x => (((SchwartzMap.evalCLM ℝ (Space dm1.succ) ℝ (basis i))
        ((fderivCLM ℝ (Space dm1.succ) ℝ) η)) x • f x) j) volume := by
    simp only [PiLp.smul_apply]
    exact (hf.pi_comp j).integrable_space _
  convert integrable_lemma i i using 2
  rename_i x
  simp only [EuclideanSpace.inner_single_right, Nat.succ_eq_add_one, conj_trivial, one_mul,
    PiLp.smul_apply, smul_eq_mul, mul_eq_mul_right_iff]
  left
  rw [deriv_eq_fderiv_basis]
  rfl

lemma integrable_isDistBounded_inner_grad_schwartzMap_spherical{dm1 : ℕ}
    {f : Space dm1.succ → EuclideanSpace ℝ (Fin dm1.succ)}
    (hf : IsDistBounded f) (η : 𝓢(Space dm1.succ, ℝ)) :
    Integrable ((fun x => ⟪f x.1, Space.grad η x.1⟫_ℝ)
      ∘ (homeomorphUnitSphereProd (Space dm1.succ)).symm)
      ((volume (α := Space dm1.succ)).toSphere.prod
      (Measure.volumeIoiPow (Module.finrank ℝ (Space dm1.succ) - 1))) := by
  have h1 : Integrable ((fun x => ⟪f x.1, Space.grad η x.1⟫_ℝ))
      (.comap (Subtype.val (p := fun x => x ∈ ({0}ᶜ : Set _))) volume) := by
    change Integrable ((fun x => ⟪f x, Space.grad η x⟫_ℝ) ∘ Subtype.val)
      (.comap (Subtype.val (p := fun x => x ∈ ({0}ᶜ : Set _))) volume)
    rw [← MeasureTheory.integrableOn_iff_comap_subtypeVal]
    apply Integrable.integrableOn
    exact integrable_isDistBounded_inner_grad_schwartzMap hf η
    simp
  have he := (MeasureTheory.Measure.measurePreserving_homeomorphUnitSphereProd
    (volume (α := Space dm1.succ)))
  rw [← he.integrable_comp_emb]
  convert h1
  simp only [Nat.succ_eq_add_one, Function.comp_apply, Homeomorph.symm_apply_apply]
  exact Homeomorph.measurableEmbedding (homeomorphUnitSphereProd (Space dm1.succ))

/-!

## B. Gradient of distributions

-/

/-!

### B.1. The definition

-/

/-- The gradient of a distribution `(Space d) →d[ℝ] ℝ` as a distribution
  `(Space d) →d[ℝ] (EuclideanSpace ℝ (Fin d))`. -/
noncomputable def distGrad {d} :
    ((Space d) →d[ℝ] ℝ) →ₗ[ℝ] (Space d) →d[ℝ] (EuclideanSpace ℝ (Fin d)) where
  toFun f := basis.repr.toContinuousLinearMap ∘L
    ((InnerProductSpace.toDual ℝ (Space d)).symm.toContinuousLinearMap).comp (fderivD ℝ f)
  map_add' f1 f2 := by
    ext x
    simp
  map_smul' a f := by
    ext x
    simp

/-!

### B.2. The gradient of inner products

-/

lemma distGrad_inner_eq {d} (f : (Space d) →d[ℝ] ℝ) (η : 𝓢(Space d, ℝ))
    (y : EuclideanSpace ℝ (Fin d)) : ⟪distGrad f η, y⟫_ℝ = fderivD ℝ f η (basis.repr.symm y) := by
  rw [distGrad]
  simp only [LinearIsometryEquiv.toLinearEquiv_symm, LinearMap.coe_mk, AddHom.coe_mk,
    ContinuousLinearMap.coe_comp', LinearMap.coe_toContinuousLinearMap', LinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toLinearEquiv, LinearIsometryEquiv.coe_symm_toLinearEquiv,
    Function.comp_apply, basis_repr_inner_eq, toDual_symm_apply]

lemma distGrad_eq_of_inner {d} (f : (Space d) →d[ℝ] ℝ)
    (g : (Space d) →d[ℝ] EuclideanSpace ℝ (Fin d))
    (h : ∀ η y, fderivD ℝ f η y = ⟪g η, basis.repr y⟫_ℝ) :
    distGrad f = g := by
  ext1 η
  apply ext_inner_right (𝕜 := ℝ) fun v => ?_
  simp [distGrad_inner_eq, h]

/-!

### B.3. The gradient as a sum over basis vectors

-/

lemma distGrad_eq_sum_basis {d} (f : (Space d) →d[ℝ] ℝ) (η : 𝓢(Space d, ℝ)) :
    distGrad f η =
      ∑ i, - f (SchwartzMap.evalCLM ℝ (Space d) ℝ (basis i) (fderivCLM ℝ (Space d) ℝ η)) •
      EuclideanSpace.single i 1 := by
  have h1 (y : EuclideanSpace ℝ (Fin d)) :
      ⟪∑ i, - f (SchwartzMap.evalCLM ℝ (Space d) ℝ (basis i) (fderivCLM ℝ (Space d) ℝ η)) •
        EuclideanSpace.single i 1, y⟫_ℝ =
      fderivD ℝ f η (basis.repr.symm y) := by
    have hy : y = ∑ i, y i • EuclideanSpace.single i 1 := by
      conv_lhs => rw [← OrthonormalBasis.sum_repr (EuclideanSpace.basisFun (Fin d) ℝ) y]
      simp
    rw [hy]
    simp [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, map_sum, map_smul, smul_eq_mul,
      Pi.single_apply, fderivD_apply]
  have hx (y : EuclideanSpace ℝ (Fin d)) : ⟪distGrad f η, y⟫_ℝ =
      ⟪∑ i, - f (SchwartzMap.evalCLM ℝ (Space d) ℝ (basis i) (fderivCLM ℝ (Space d) ℝ η)) •
        EuclideanSpace.single i 1, y⟫_ℝ := by
    rw [distGrad_inner_eq, h1]
  have h1 : ∀ y, ⟪distGrad f η -
    (∑ i, - f (SchwartzMap.evalCLM ℝ (Space d) ℝ (basis i) (fderivCLM ℝ (Space d) ℝ η)) •
      EuclideanSpace.single i 1), y⟫_ℝ = 0 := by
    intro y
    rw [inner_sub_left, hx y]
    simp
  have h2 := h1 (distGrad f η -
    (∑ i, - f (SchwartzMap.evalCLM ℝ (Space d) ℝ (basis i) (fderivCLM ℝ (Space d) ℝ η)) •
    EuclideanSpace.single i 1))
  rw [inner_self_eq_zero, sub_eq_zero] at h2
  rw [h2]

/-!

### B.4. The underlying function of the gradient distribution

-/

lemma distGrad_toFun_eq_distDeriv {d} (f : (Space d) →d[ℝ] ℝ) :
    (distGrad f).toFun = fun ε => WithLp.toLp 2 fun i => distDeriv i f ε := by
  ext ε i
  simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, ContinuousLinearMap.coe_coe]
  rw [distGrad_eq_sum_basis]
  simp only [neg_smul, Finset.sum_neg_distrib, PiLp.neg_apply, WithLp.ofLp_sum, WithLp.ofLp_smul,
    EuclideanSpace.ofLp_single, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  rfl

/-!

### B.5. The gradient applied to a Schwartz function

-/

lemma distGrad_apply {d} (f : (Space d) →d[ℝ] ℝ) (ε : 𝓢(Space d, ℝ)) :
    (distGrad f) ε = fun i => distDeriv i f ε := by
  change (distGrad f).toFun ε = fun i => distDeriv i f ε
  rw [distGrad_toFun_eq_distDeriv]

end Space
