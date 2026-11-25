/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Physlib.SpaceAndTime.WaveVectorSpace.DualPairing
/-!

# Fourier transforms between `Space` and `WaveVectorSpace`

## i. Overview

The purpose of this module is to provide a means to work with Fourier transforms in a way
that is both dimensionally consistent and flexible enough to allow various conventions.

The two main definitions are `fourierIntegral a b : (Space d → E) → WaveVectorSpace d → E`
and `fourierIntegralInv a b : (WaveVectorSpace d → E) → Space d → E` which amount to the following
integral transformations depending on two parameters `a b : ℝ`:

$$
\tilde{f}(k) :=
  \left(\frac{|b|}{(2\pi)^{1-a}}\right)^{d/2}
  \int f(x)\,\mathrm{e}^{\mathrm{i}bk\cdot x} \,\mathrm{d}^dx
\;,\qquad
f(x) :=
  \left(\frac{|b|}{(2\pi)^{1+a}}\right)^{d/2}
  \int \tilde{f}(k)\,\mathrm{e}^{-\mathrm{i}bk\cdot x} \,\mathrm{d}^dk
\;.
$$

These are implemented as rescaled/dilated versions of `VectorFourier.fourierIntegral`
and most results require that the input function be integrable.

Results which hold for all `a` and `b` should be written in terms of `fourierIntegral a b`.
Opening the `FourierTransform` namespace allows one to use the notation `𝓕` and `𝓕⁻`
with default values $(a,b) = (0,1)$; to use this notation with a different convention include
the line `open scoped FourierTransform[a][b]` (*e.g.* `open scoped FourierTransform1n1`
for $(a,b) = (1,-1)$). If a common convention is missing it can be added below in section B.

## ii. Key results

- `fourierIntegral a b` : the Fourier integral with real parameters `a` and `b`,
  corresponding to a choice of convention, which maps a function `f : Space d → E`
  to its Fourier transform of type `WaveVectorSpace d → E`.
- `fourierIntegralInv a b` : the inverse Fourier integral with real parameters `a` and `b`,
  corresponding to a choice of convention, which maps a function `g : WaveVectorSpace d → E`
  to its Fourier transform of type `Space d → E`.
- `deriv_fourierIntegral` / `deriv_fourierIntegralInv` : for a suitably nice function
  `f : Space d → E` the derivative along the `i`ᵗʰ coordinate direction of its Fourier integral
  is the Fourier integral of the function `x ↦ (b * I * x i) • f x`, and similarly for functions
  `WaveVectorSpace d → E` and the inverse Fourier integral.
- `fourierIntegral_deriv` / `fourierIntegralInv_deriv` : for a suitably nice function
  `f : Space d → E` the Fourier integral of its `i`ᵗʰ derivative is `-b * I * k i` times its Fourier
  integral, and similarly for functions `WaveVectorSpace d → E` and the inverse Fourier integral.
- `fourierIntegralInv_fourierIntegral_eq` / `fourierIntegral_fourierIntegralInv_eq` :
  for suitably nice functions `f : Space d → E` and `g : WaveVectorSpace d → E`,
  the identities `fourierIntegralInv a b (fourierIntegral a b f) = f`
  and `fourierIntegral a b (fourierIntegralInv a b g) = g`, respectively.

## iii. Table of contents

- A. Fourier integrals
  - A.1. Two-parameter definitions
  - A.2. Basic properties
    - A.2.1. Linearity
    - A.2.2. Continuity
    - A.2.3. Integration of continuous linear maps
  - A.3. Derivatives
    - A.3.1. Fréchet derivatives
    - A.3.2. Partial derivatives
  - A.4. Inversion
- B. Fourier instances
  - B.1. `(a, b) = (0, 1)` (default)
  - B.2. `(a, b) = (1, -1)`

## iv. References

The parametrization in terms of `a b : ℝ` follows that given here:

* Weisstein, Eric W. "Fourier Transform." From MathWorld--A Wolfram Resource.
  [ref: mathworld_fourier_transform]

-/

@[expose] public section

variable {d : ℕ}

namespace WaveVectorSpace

/-!
## A. Fourier integrals
-/

section FourierIntegral

open Complex MeasureTheory Real
open scoped FourierTransform

variable (a b : ℝ) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-!
### A.1. Two-parameter definitions
-/

/-- The Fourier integral over `Space`,

`(|b| / (2 * π) ^ (1 - a)) ^ (d / 2 : ℝ) • ∫ x, exp (b * (k ⬝ᵥ x) * I) • f x ∂volume`,

parametrized by `a b : ℝ`.
-/
noncomputable def fourierIntegral (f : Space d → E) (k : WaveVectorSpace d) : E :=
  (|b| / (2 * π) ^ (1 - a)) ^ (d / 2 : ℝ)
    • VectorFourier.fourierIntegral 𝐞 volume (-(b / (2 * π)) • pairingCLM.flip).toLinearMap₁₂ f k

lemma fourierIntegral_def (f : Space d → E) :
    fourierIntegral a b f
      = (|b| / (2 * π) ^ (1 - a)) ^ (d / 2 : ℝ)
        • VectorFourier.fourierIntegral 𝐞 volume
          (-(b / (2 * π)) • pairingCLM.flip).toLinearMap₁₂ f :=
  rfl

lemma fourierIntegral_eq (f : Space d → E) (k : WaveVectorSpace d) :
    fourierIntegral a b f k
      = (|b| / (2 * π) ^ (1 - a)) ^ (d / 2 : ℝ) • ∫ x : Space d, cexp (b * (k ⬝ᵥ x) * I) • f x := by
  simp [fourierIntegral_def, VectorFourier.fourierIntegral, fourierChar, pairingCLM_apply_eq_dual,
    dual_apply, Circle.smul_def, ← mul_assoc, mul_div_cancel₀]

open scoped RealInnerProductSpace in
/-- Expresses the Fourier integral in terms of the Fourier transform on Euclidean space
`𝓢 : (EuclideanSpace ℝ (Fin d) → E) → EuclideanSpace ℝ (Fin d) → E`
by mapping through the standard bases of `Space d` and `WaveVectorSpace d`. -/
lemma fourierIntegral_eq_smul_fourier_comp (f : Space d → E) :
    fourierIntegral a b f
      = (|b| / (2 * π) ^ (1 - a)) ^ (d / 2 : ℝ)
        • 𝓕 (f ∘ Space.basis.repr.symm) ∘ (-(b / (2 * π)) • basis.repr.toLinearMap) := by
  ext k
  rw [fourierIntegral_eq]
  congr 1
  calc
    _ = ∫ x : Space d, Circle.exp (b * k ⬝ᵥ x) • f x := by simp [Circle.smul_def]
    _ = ∫ v, Circle.exp (b * ⟪v, basis.repr k⟫) • f (Space.basis.repr.symm v) := Eq.symm <|
      Space.basis.repr.symm.measurePreserving.integral_comp
        Space.basis.repr.symm.toMeasurableEquiv.measurableEmbedding
          fun x ↦ Circle.exp (b * ⟪Space.basis.repr x, basis.repr k⟫) • f x
    _ = (𝓕 _ ∘ _) k := by
      simp [fourier_eq, fourierChar, inner_smul_right, ← mul_assoc, mul_div_cancel₀]

/-- The inverse Fourier integral over `WaveVectorSpace`,

`(|b| / (2 * π) ^ (1 + a)) ^ (d / 2 : ℝ) • ∫ k, exp (-b * (k ⬝ᵥ x) * I) • g k ∂volume`,

parametrized by `a b : ℝ`.
-/
noncomputable def fourierIntegralInv (g : WaveVectorSpace d → E) (x : Space d) : E :=
  (|b| / (2 * π) ^ (1 + a)) ^ (d / 2 : ℝ)
    • VectorFourier.fourierIntegral 𝐞 volume ((b / (2 * π)) • pairingCLM).toLinearMap₁₂ g x

lemma fourierIntegralInv_def (g : WaveVectorSpace d → E) :
    fourierIntegralInv a b g
      = (|b| / (2 * π) ^ (1 + a)) ^ (d / 2 : ℝ)
        • VectorFourier.fourierIntegral 𝐞 volume ((b / (2 * π)) • pairingCLM).toLinearMap₁₂ g :=
  rfl

lemma fourierIntegralInv_eq (g : WaveVectorSpace d → E) (x : Space d) :
    fourierIntegralInv a b g x
      = (|b| / (2 * π) ^ (1 + a)) ^ (d / 2 : ℝ)
        • ∫ k : WaveVectorSpace d, cexp (-b * (k ⬝ᵥ x) * I) • g k := by
  simp [fourierIntegralInv_def, VectorFourier.fourierIntegral, pairingCLM_apply_eq_dual,
    fourierChar, dual_apply, Circle.smul_def, Complex.exp_neg, ← mul_assoc, mul_div_cancel₀]

open scoped RealInnerProductSpace in
/-- Expresses the inverse Fourier integral in terms of the inverse Fourier transform
on Euclidean space `𝓢 : (EuclideanSpace ℝ (Fin d) → E) → EuclideanSpace ℝ (Fin d) → E`
by mapping through the standard bases of `Space d` and `WaveVectorSpace d`. -/
lemma fourierIntegralInv_eq_smul_fourierInv_comp (g : WaveVectorSpace d → E) :
    fourierIntegralInv a b g
      = (|b| / (2 * π) ^ (1 + a)) ^ (d / 2 : ℝ)
        • 𝓕⁻ (g ∘ basis.repr.symm) ∘ (-(b / (2 * π)) • Space.basis.repr.toLinearMap) := by
  ext x
  rw [fourierIntegralInv_eq]
  congr 1
  calc
    _ = ∫ k : WaveVectorSpace d, Circle.exp (-b * x ⬝ᵥ k) • g k := by
      simp [Circle.smul_def, Complex.exp_neg, dotProduct_comm]
    _ = ∫ v, Circle.exp (-b * ⟪v, Space.basis.repr x⟫) • g (basis.repr.symm v) := Eq.symm <|
      basis.repr.symm.measurePreserving.integral_comp
        basis.repr.symm.toMeasurableEquiv.measurableEmbedding
          fun k ↦ Circle.exp (-b * ⟪basis.repr k, Space.basis.repr x⟫) • g k
    _ = (𝓕⁻ _ ∘ _) x := by
      simp [fourierInv_eq, fourierChar, inner_smul_right, ← mul_assoc, mul_div_cancel₀]

/-!
### A.2. Basic properties
-/

lemma fourierIntegral_congr_ae {f₁ f₂ : Space d → E} (hf : f₁ =ᵐ[volume] f₂) :
    fourierIntegral a b f₁ = fourierIntegral a b f₂ := by
  rw [fourierIntegral_def, fourierIntegral_def, VectorFourier.fourierIntegral_congr_ae _ _ _ hf]

lemma fourierIntegralInv_congr_ae {g₁ g₂ : WaveVectorSpace d → E} (hg : g₁ =ᵐ[volume] g₂) :
    fourierIntegralInv a b g₁ = fourierIntegralInv a b g₂ := by
  rw [fourierIntegralInv_def, fourierIntegralInv_def,
    VectorFourier.fourierIntegral_congr_ae _ _ _ hg]

/-!
#### A.2.1. Linearity
-/

lemma fourierIntegral_const_smul (f : Space d → E) (c : ℂ) :
    fourierIntegral a b (c • f) = c • fourierIntegral a b f := by
  simp only [fourierIntegral_def, VectorFourier.fourierIntegral_const_smul, smul_comm c]

lemma fourierIntegralInv_const_smul (f : WaveVectorSpace d → E) (c : ℂ) :
    fourierIntegralInv a b (c • f) = c • fourierIntegralInv a b f := by
  simp only [fourierIntegralInv_def, VectorFourier.fourierIntegral_const_smul, smul_comm c]

lemma fourierIntegral_add {f₁ f₂ : Space d → E} (hf₁ : Integrable f₁) (hf₂ : Integrable f₂) :
    fourierIntegral a b (f₁ + f₂) = fourierIntegral a b f₁ + fourierIntegral a b f₂ := by
  simp only [fourierIntegral_def, ← smul_add]
  rw [VectorFourier.fourierIntegral_add continuous_fourierChar
    (-(b / (2 * π)) • pairingCLM.flip).continuous₂ hf₁ hf₂]

lemma fourierIntegralInv_add
    {g₁ g₂ : WaveVectorSpace d → E} (hg₁ : Integrable g₁) (hg₂ : Integrable g₂) :
    fourierIntegralInv a b (g₁ + g₂) = fourierIntegralInv a b g₁ + fourierIntegralInv a b g₂ := by
  simp only [fourierIntegralInv_def, ← smul_add]
  rw [VectorFourier.fourierIntegral_add continuous_fourierChar
    ((b / (2 * π)) • pairingCLM).continuous₂ hg₁ hg₂]

/-!
#### A.2.2. Continuity
-/

lemma fourierIntegral_continuous {f : Space d → E} (hf : Integrable f) :
    Continuous (fourierIntegral a b f) :=
  VectorFourier.fourierIntegral_continuous continuous_fourierChar
    (-(b / (2 * π)) • pairingCLM.flip).continuous₂ hf |>.const_smul _

lemma fourierIntegralInv_continuous {g : WaveVectorSpace d → E} (hg : Integrable g) :
    Continuous (fourierIntegralInv a b g) :=
  VectorFourier.fourierIntegral_continuous continuous_fourierChar
    ((b / (2 * π)) • pairingCLM).continuous₂ hg |>.const_smul _

/-!
#### A.2.3. Integration of continuous linear maps
-/

section IntegrandCLM

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Given a CLM-valued function of space, `f : Space d → F →L[ℝ] E`,
evaluating its Fourier integral at `v : F` is the same as taking
the Fourier integral of `x ↦ f x v`. -/
lemma fourierIntegral_continuousLinearMap_apply
    {f : Space d → F →L[ℝ] E} (hf : Integrable f) (k : WaveVectorSpace d) (v : F) :
    fourierIntegral a b f k v = fourierIntegral a b (f · v) k := by
  simp only [fourierIntegral_def, Pi.smul_apply, smul_apply,
    VectorFourier.fourierIntegral_continuousLinearMap_apply continuous_fourierChar hf]

/-- Given a CLM-valued function of wavevector, `g : WaveVectorSpace d → F →L[ℝ] E`,
evaluating its inverse Fourier integral at `v : F` is the same as taking
the inverse Fourier integral of `k ↦ g k v`. -/
lemma fourierIntegralInv_continuousLinearMap_apply
    {g : WaveVectorSpace d → F →L[ℝ] E} (hg : Integrable g) (x : Space d) (v : F) :
    fourierIntegralInv a b g x v = fourierIntegralInv a b (g · v) x := by
  simp only [fourierIntegralInv_def, Pi.smul_apply, smul_apply,
    VectorFourier.fourierIntegral_continuousLinearMap_apply continuous_fourierChar hg]

end IntegrandCLM

/-!
### A.3. Derivatives
-/

/-!
#### A.3.1. Fréchet derivatives
-/

lemma fderiv_fourierIntegral
    {f : Space d → E} (hf : Integrable f) (hf' : Integrable fun x ↦ ‖x‖ * ‖f x‖) :
    fderiv ℝ (fourierIntegral a b f)
      = fourierIntegral a b (fun x ↦ (b * I) • x.dual.smulRight (f x)) := by
  rw [fourierIntegral_def, fderiv_const_smul_field, VectorFourier.fderiv_fourierIntegral _ hf hf']
  congr with x k
  calc
    _ = (2 * π * I * (b / (2 * π) * pairingCLM k x)) • f x := by simp [← coe_smul, smul_smul]
    _ = (b * I * pairingCLM k x) • f x := by field_simp
    _ = (b * I) • (k ⬝ᵥ x) • f x := by simp [← coe_smul, smul_smul]

lemma fderiv_fourierIntegralInv
    {g : WaveVectorSpace d → E} (hg : Integrable g) (hg' : Integrable (fun k ↦ ‖k‖ * ‖g k‖)) :
    fderiv ℝ (fourierIntegralInv a b g)
      = fourierIntegralInv a b (fun k ↦ -(b * I) • k.dual.smulRight (g k)) := by
  rw [fourierIntegralInv_def, fderiv_const_smul_field,
    VectorFourier.fderiv_fourierIntegral _ hg hg']
  congr with k x
  calc
    _ = -(2 * π * I * (b / (2 * π) * pairingCLM k x)) • g k := by simp [← coe_smul, smul_smul]
    _ = -(b * I * pairingCLM k x) • g k := by field_simp
    _ = -(b * I) • (k ⬝ᵥ x) • g k := by simp [← coe_smul, smul_smul]

lemma fourierIntegral_fderiv {f : Space d → E} (hf : Integrable f) (hf' : Differentiable ℝ f)
    (hf'' : Integrable (fderiv ℝ f)) (k : WaveVectorSpace d) :
    fourierIntegral a b (fderiv ℝ f) k = -(b * I) • k.dual.smulRight (fourierIntegral a b f k) := by
  ext
  simp only [fourierIntegral_def, VectorFourier.fourierIntegral_fderiv _ hf hf' hf'']
  simp [← coe_smul, smul_smul, ← mul_assoc _ (b / (2 * π) : ℂ), ← mul_comm I, mul_assoc I (2 * π),
    mul_div_cancel₀, mul_rotate', dual_apply]

lemma fourierIntegralInv_fderiv {g : WaveVectorSpace d → E}
    (hg : Integrable g) (hg' : Differentiable ℝ g) (hg'' : Integrable (fderiv ℝ g)) (x : Space d) :
    fourierIntegralInv a b (fderiv ℝ g) x
      = (b * I) • x.dual.smulRight (fourierIntegralInv a b g x) := by
  ext
  simp only [fourierIntegralInv_def, VectorFourier.fourierIntegral_fderiv _ hg hg' hg'']
  simp [← coe_smul, smul_smul, ← mul_assoc _ (b / (2 * π) : ℂ), ← mul_comm I, mul_assoc I (2 * π),
    mul_div_cancel₀, mul_rotate', Space.dual_apply]

/-!
#### A.3.2. Partial derivatives
-/

/-- The partial derivative of the Fourier transform of `f` along coordinate `i`
is the Fourier transform of `x ↦ (b * I * x i) • f x`, provided both integrals exist. -/
lemma deriv_fourierIntegral (i : Fin d)
    {f : Space d → E} (hf : Integrable f) (hf' : Integrable fun x ↦ ‖x‖ * ‖f x‖) :
    ∂[i] (fourierIntegral a b f) = fourierIntegral a b fun x ↦ (b * I * x i) • f x := by
  have h : Integrable (fun x : Space d ↦ (b * I) • x.dual.smulRight (f x)) :=
    hf'.smul b |>.congr' (by fun_prop) <| by simp [norm_smul]
  ext
  simp [deriv_eq, fderiv_fourierIntegral, fourierIntegral_continuousLinearMap_apply,
    Space.dual_apply, dotProduct, ← nsmul_eq_mul, ← coe_smul, smul_smul, hf, hf', h]

/-- The partial derivative of the inverse Fourier transform of `g` along coordinate `i`
is the inverse Fourier transform of `k ↦ (-b * I * k i) • g k`, provided both integrals exist. -/
lemma deriv_fourierIntegralInv (i : Fin d)
    {g : WaveVectorSpace d → E} (hg : Integrable g) (hg' : Integrable fun k ↦ ‖k‖ * ‖g k‖) :
    ∂[i] (fourierIntegralInv a b g) = fourierIntegralInv a b fun k ↦ -(b * I * k i) • g k := by
  have h : Integrable (fun k : WaveVectorSpace d ↦ -(b * I) • k.dual.smulRight (g k)) :=
    hg'.smul b |>.congr' (by fun_prop) <| by simp [norm_smul]
  ext
  simp [Space.deriv_eq, fderiv_fourierIntegralInv, fourierIntegralInv_continuousLinearMap_apply,
    dual_apply, dotProduct, Space.basis_apply, ← coe_smul, smul_smul, hg, hg', h]

/-- The Fourier transform of the partial derivative of `f` along coordinate `i`
is `-b * I * kᵢ` times the Fourier transform of `f`.

That is, the Fourier transform maps derivatives to multiplication. -/
lemma fourierIntegral_deriv (i : Fin d) {f : Space d → E}
    (hf : Integrable f) (hf' : Differentiable ℝ f) (hf'' : Integrable (fderiv ℝ f)) :
    fourierIntegral a b (∂[i] f) = -(b * I) • coord i • fourierIntegral a b f := by
  ext
  simp [Space.deriv_eq_fderiv_fun, coord_apply, dual_apply, fourierIntegral_fderiv, dotProduct, hf',
    ← fourierIntegral_continuousLinearMap_apply, Space.basis_apply, hf, hf'', ← coe_smul, smul_smul]

/-- The inverse Fourier transform of the partial derivative of `g` along coordinate `i`
is `b * I * xᵢ` times the inverse Fourier transform of `g`.

That is, the inverse Fourier transform maps derivatives to multiplication. -/
lemma fourierIntegralInv_deriv (i : Fin d) {g : WaveVectorSpace d → E}
    (hg : Integrable g) (hg' : Differentiable ℝ g) (hg'' : Integrable (fderiv ℝ g)) :
    fourierIntegralInv a b (∂[i] g) = (b * I) • Space.coord i • fourierIntegralInv a b g := by
  ext
  simp [deriv_eq_fun, ← fourierIntegralInv_continuousLinearMap_apply, fourierIntegralInv_fderiv,
    Space.coord_apply, Space.dual_apply, dotProduct, ← coe_smul, smul_smul, ← nsmul_eq_mul,
    hg, hg', hg'']

/-!
### A.4. Inversion
-/

section Inversion

local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

local instance : FourierSMul ℝ (ℝᵈ → E) (ℝᵈ → E) where
  fourier_smul c _ := by ext; simp [fourier_eq, smul_comm _ c, integral_smul]

local instance : FourierInvSMul ℝ (ℝᵈ → E) (ℝᵈ → E) where
  fourierInv_smul c _ := by ext; simp [fourierInv_eq, smul_comm _ c, integral_smul]

/-- Behavior of the Fourier transform `𝓕 : (ℝᵈ → E) → ℝᵈ → E` under dilations. -/
private lemma fourier_comp_smul_id {c : ℝ} (hc : c ≠ 0) (f : ℝᵈ → E) :
    𝓕 (f ∘ (c⁻¹ • id)) = (|c| ^ d) • 𝓕 f ∘ (c • id)  := by
  ext v
  have := Measure.integral_comp_smul volume (fun w ↦ 𝐞 (-inner ℝ (c • w) v) • f w) c⁻¹
  simp_all [fourier_eq, smul_smul, inner_smul_left, inner_smul_right]

/-- Behavior of the inverse Fourier transform `𝓕⁻ : (ℝᵈ → E) → ℝᵈ → E` under dilations. -/
private lemma fourierInv_comp_smul_id {c : ℝ} (hc : c ≠ 0) (f : ℝᵈ → E) :
    𝓕⁻ (f ∘ (c⁻¹ • id)) = (|c| ^ d) • 𝓕⁻ f ∘ (c • id)  := by
  ext v
  have := Measure.integral_comp_smul volume (fun w ↦ 𝐞 (inner ℝ (c • w) v) • f w) c⁻¹
  simp_all [fourierInv_eq, smul_smul, inner_smul_left, inner_smul_right]

variable {b}

/-- The Fourier inversion formula:
`𝓕⁻ (𝓕 f) = f` for a suitably nice function `f : Space d → E`. -/
lemma fourierIntegralInv_fourierIntegral_eq (hb : b ≠ 0) [CompleteSpace E] {f : Space d → E}
    (h : Continuous f) (hf : Integrable f) (hf' : Integrable (fourierIntegral a b f)) :
    fourierIntegralInv a b (fourierIntegral a b f) = f := by
  -- The heavy lifting in this proof is done by `Continuous.fourierInv_fourier_eq`.
  -- What follows is mostly dealing with the dilations by `c := -b/(2π)`
  -- and the linear isometries with Euclidean space provided by the standard bases.
  let c : ℝ := -(b / (2 * π))
  have hc : c ≠ 0 := by simpa [c]
  let c₁ : ℝ := (|b| / (2 * π) ^ (1 + a)) ^ (d / 2 : ℝ)
  let c₂ : ℝ := (|b| / (2 * π) ^ (1 - a)) ^ (d / 2 : ℝ)
  have hc₂ : c₂ ≠ 0 := ne_of_gt <| rpow_pos_of_pos (by positivity) _
  have hc₁₂ : c₁ * c₂ = |c| ^ d := by
    rw [← Real.mul_rpow (by bound) (by bound), div_mul_div_comm, ← Real.rpow_add (by bound),
      div_rpow (by bound) (by bound), ← pow_two, ← Real.rpow_natCast, add_add_sub_cancel]
    simp only [← Real.rpow_mul, abs_nonneg b, one_add_one_eq_two, show 0 ≤ 2 * π by bound]
    simp [mul_div_cancel₀, c, abs_div, div_pow]
  let e₁ : Space d ≃ₗᵢ[ℝ] ℝᵈ := Space.basis.repr
  let e₂ : WaveVectorSpace d ≃ₗᵢ[ℝ] ℝᵈ := basis.repr
  have h_int : Integrable (f ∘ e₁.symm ∘ (c⁻¹ • id)) := by
    have := (e₁.symm.measurePreserving.integrable_comp hf.aestronglyMeasurable).mpr hf
    apply (MeasureTheory.integrable_comp_smul_iff _ _ hc).mp
    simpa [smul_smul, inv_mul_cancel₀ hc]
  have h𝓕_int : Integrable (𝓕 (f ∘ e₁.symm ∘ (c⁻¹ • id))) := by
    refine (e₂.measurePreserving.integrable_comp ?_).mp ?_
    · apply Continuous.aestronglyMeasurable
      exact VectorFourier.fourierIntegral_continuous continuous_fourierChar continuous_inner h_int
    · refine hf'.smul ((|c| ^ d) * c₂⁻¹) |>.congr <| Eq.eventuallyEq ?_
      ext
      rw [fourierIntegral_eq_smul_fourier_comp, ← Function.comp_assoc, fourier_comp_smul_id hc]
      simp [smul_smul, mul_assoc, inv_mul_cancel₀ hc₂, c, c₂, e₁, e₂]
  rw [fourierIntegral_eq_smul_fourier_comp, fourierIntegralInv_eq_smul_fourierInv_comp]
  calc
    _ = c₁ • 𝓕⁻ ((c₂ • (𝓕 (f ∘ e₁.symm) ∘ (c • ⇑e₂))) ∘ e₂.symm) ∘ (c • ⇑e₁) := rfl
    _ = |c| ^ d • 𝓕⁻ (𝓕 (f ∘ e₁.symm) ∘ (c • id)) ∘ (c • ⇑e₁) := by
      simp [Pi.smul_comp, smul_smul, Function.comp_assoc, hc₁₂]
    _ = 𝓕⁻ (𝓕 (f ∘ e₁.symm ∘ (c⁻¹ • id))) ∘ (c • ⇑e₁) := by
      simp [fourier_comp_smul_id hc, Pi.smul_comp, ← Function.comp_assoc]
    _ = (f ∘ e₁.symm ∘ (c⁻¹ • id)) ∘ (c • ⇑e₁) := by
      rw [Continuous.fourierInv_fourier_eq (by fun_prop) h_int h𝓕_int]
    _ = f := by ext; simp [smul_smul, inv_mul_cancel₀ hc]

/-- The Fourier inversion formula:
`𝓕 (𝓕⁻ g) = g` for a suitably nice function `g : WaveVectorSpace d → E`. -/
lemma fourierIntegral_fourierIntegralInv_eq
    (hb : b ≠ 0) [CompleteSpace E] {g : WaveVectorSpace d → E}
    (h : Continuous g) (hg : Integrable g) (hg' : Integrable (fourierIntegralInv a b g)) :
    fourierIntegral a b (fourierIntegralInv a b g) = g := by
  -- The heavy lifting in this proof is done by `Continuous.fourier_fourierInv_eq`.
  -- What follows is mostly dealing with the dilations by `c := -b/(2π)`
  -- and the linear isometries with Euclidean space provided by the standard bases.
  let c : ℝ := -(b / (2 * π))
  have hc : c ≠ 0 := by simpa [c]
  let c₁ : ℝ := (|b| / (2 * π) ^ (1 + a)) ^ (d / 2 : ℝ)
  let c₂ : ℝ := (|b| / (2 * π) ^ (1 - a)) ^ (d / 2 : ℝ)
  have hc₁ : c₁ ≠ 0 := ne_of_gt <| rpow_pos_of_pos (by positivity) _
  have hc₂₁ : c₂ * c₁ = |c| ^ d := by
    rw [← Real.mul_rpow (by bound) (by bound), div_mul_div_comm, ← Real.rpow_add (by bound),
      div_rpow (by bound) (by bound), ← pow_two, ← Real.rpow_natCast, sub_add_add_cancel]
    simp only [← Real.rpow_mul, abs_nonneg b, one_add_one_eq_two, show 0 ≤ 2 * π by bound]
    simp [mul_div_cancel₀, c, abs_div, div_pow]
  let e₁ : Space d ≃ₗᵢ[ℝ] ℝᵈ := Space.basis.repr
  let e₂ : WaveVectorSpace d ≃ₗᵢ[ℝ] ℝᵈ := basis.repr
  have h_int : Integrable (g ∘ e₂.symm ∘ (c⁻¹ • id)) := by
    have := (e₂.symm.measurePreserving.integrable_comp hg.aestronglyMeasurable).mpr hg
    apply (MeasureTheory.integrable_comp_smul_iff _ _ hc).mp
    simpa [smul_smul, inv_mul_cancel₀ hc]
  have h𝓕_int : Integrable (𝓕 (g ∘ e₂.symm ∘ (c⁻¹ • id))) := by
    refine (e₁.measurePreserving.integrable_comp ?_).mp ?_
    · apply Continuous.aestronglyMeasurable
      exact VectorFourier.fourierIntegral_continuous continuous_fourierChar continuous_inner h_int
    · refine hg'.comp_neg.smul ((|c| ^ d) * c₁⁻¹) |>.congr <| Eq.eventuallyEq ?_
      ext
      rw [fourierIntegralInv_eq_smul_fourierInv_comp, ← Function.comp_assoc,
        fourier_comp_smul_id hc]
      simp [fourierInv_eq_fourier_neg, smul_smul, mul_assoc, inv_mul_cancel₀ hc₁, c, c₁, e₁, e₂]
  rw [fourierIntegral_eq_smul_fourier_comp, fourierIntegralInv_eq_smul_fourierInv_comp]
  calc
    _ = c₂ • 𝓕 ((c₁ • (𝓕⁻ (g ∘ e₂.symm) ∘ (c • ⇑e₁))) ∘ e₁.symm) ∘ (c • ⇑e₂) := rfl
    _ = |c| ^ d • 𝓕 (𝓕⁻ (g ∘ e₂.symm) ∘ (c • id)) ∘ (c • ⇑e₂) := by
      simp [Pi.smul_comp, smul_smul, Function.comp_assoc, hc₂₁]
    _ = 𝓕 (𝓕⁻ (g ∘ e₂.symm ∘ (c⁻¹ • id))) ∘ (c • ⇑e₂) := by
      simp [fourierInv_comp_smul_id hc, Pi.smul_comp, ← Function.comp_assoc]
    _ = (g ∘ e₂.symm ∘ (c⁻¹ • id)) ∘ (c • ⇑e₂) := by
      rw [Continuous.fourier_fourierInv_eq (by fun_prop) h_int h𝓕_int]
    _ = g := by ext; simp [smul_smul, inv_mul_cancel₀ hc]

end Inversion

end FourierIntegral

end WaveVectorSpace

/-!
## B. Fourier instances
-/

namespace FourierTransform

noncomputable section FourierInstances

open WaveVectorSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-!
### B.1. `(a, b) = (0, 1)` (default)

$$
\tilde{f}(k) := \frac{1}{(2\pi)^{d/2}} \int f(x)\,\mathrm{e}^{\mathrm{i}k\cdot x} \,\mathrm{d}x
\;,\qquad
f(x) := \frac{1}{(2\pi)^{d/2}} \int \tilde{f}(k)\,\mathrm{e}^{-\mathrm{i}k\cdot x} \,\mathrm{d}k
$$
-/

/-- Notation for the Fourier transform `fourierIntegral 0 1`. -/
scoped instance : FourierTransform (Space d → E) (WaveVectorSpace d → E) where
  fourier := fourierIntegral 0 1

/-- Notation for the inverse Fourier transform `fourierIntegralInv 0 1`. -/
scoped instance : FourierTransformInv (WaveVectorSpace d → E) (Space d → E) where
  fourierInv := fourierIntegralInv 0 1


/-!
### B.2. `(a, b) = (1, -1)`

$$
\tilde{f}(k) := \int f(x)\,\mathrm{e}^{-\mathrm{i}k\cdot x} \,\mathrm{d}x
\;,\qquad
f(x) := \frac{1}{(2\pi)^d} \int \tilde{f}(k)\,\mathrm{e}^{\mathrm{i}k\cdot x} \,\mathrm{d}k
$$
-/

namespace FourierTransform1n1

/-- Notation for the Fourier transform `fourierIntegral 1 (-1)`. -/
scoped instance : FourierTransform (Space d → E) (WaveVectorSpace d → E) where
  fourier := fourierIntegral 1 (-1)

/-- Notation for the inverse Fourier transform `fourierIntegralInv 1 (-1)`. -/
scoped instance : FourierTransformInv (WaveVectorSpace d → E) (Space d → E) where
  fourierInv := fourierIntegralInv 1 (-1)

end FourierTransform1n1

end FourierInstances

end FourierTransform
