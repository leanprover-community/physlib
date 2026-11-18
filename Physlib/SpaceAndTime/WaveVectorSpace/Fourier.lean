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
  \sqrt{\frac{|b|}{(2\pi)^{1-a}}}
  \int f(x)\,\mathrm{e}^{\mathrm{i}bk\cdot x} \,\mathrm{d}^dx
\;,\qquad
f(x) :=
  \sqrt{\frac{|b|}{(2\pi)^{1+a}}}
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

## iii. Table of contents

- A. Fourier integrals
  - A.1. Two-parameter definitions
  - A.2. Basic properties
    - A.2.1. Linearity
    - A.2.2. Continuity
    - A.2.3. Integration of continuous linear maps
  - A.3. Derivatives
    - A.3.1. Fourier multipliers
    - A.3.2. Fréchet derivatives
    - A.3.3. Partial derivatives
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

`√(|b| / (2 * π) ^ (1 - a)) • ∫ x, exp (b * (k ⬝ᵥ x) * I) • f x ∂volume`,

parametrized by `a b : ℝ`.
-/
noncomputable def fourierIntegral (f : Space d → E) (k : WaveVectorSpace d) : E :=
  √(|b| / (2 * π) ^ (1 - a))
    • VectorFourier.fourierIntegral 𝐞 volume (-(b / (2 * π)) • pairingCLM.flip).toLinearMap₁₂ f k

lemma fourierIntegral_def (f : Space d → E) :
    fourierIntegral a b f
      = √(|b| / (2 * π) ^ (1 - a))
        • VectorFourier.fourierIntegral 𝐞 volume
          (-(b / (2 * π)) • pairingCLM.flip).toLinearMap₁₂ f :=
  rfl

lemma fourierIntegral_eq (f : Space d → E) (k : WaveVectorSpace d) :
    fourierIntegral a b f k
      = √(|b| / (2 * π) ^ (1 - a)) • ∫ x : Space d, cexp (b * (k ⬝ᵥ x) * I) • f x := by
  simp [fourierIntegral_def, VectorFourier.fourierIntegral, fourierChar, pairingCLM_apply_eq_dual,
    dual_apply, Circle.smul_def, ← mul_assoc, mul_div_cancel₀]

/-- The inverse Fourier integral over `WaveVectorSpace`,

`√(|b| / (2 * π) ^ (1 + a)) • ∫ k, exp (-b * (k ⬝ᵥ x) * I) • g k ∂volume`,

parametrized by `a b : ℝ`.
-/
noncomputable def fourierIntegralInv (g : WaveVectorSpace d → E) (x : Space d) : E :=
  √(|b| / (2 * π) ^ (1 + a))
    • VectorFourier.fourierIntegral 𝐞 volume ((b / (2 * π)) • pairingCLM).toLinearMap₁₂ g x

lemma fourierIntegralInv_def (g : WaveVectorSpace d → E) :
    fourierIntegralInv a b g
      = √(|b| / (2 * π) ^ (1 + a))
        • VectorFourier.fourierIntegral 𝐞 volume ((b / (2 * π)) • pairingCLM).toLinearMap₁₂ g :=
  rfl

lemma fourierIntegralInv_eq (g : WaveVectorSpace d → E) (x : Space d) :
    fourierIntegralInv a b g x
      = √(|b| / (2 * π) ^ (1 + a)) • ∫ k : WaveVectorSpace d, cexp (-b * (k ⬝ᵥ x) * I) • g k := by
  simp [fourierIntegralInv_def, VectorFourier.fourierIntegral, pairingCLM_apply_eq_dual,
    fourierChar, dual_apply, Circle.smul_def, Complex.exp_neg, ← mul_assoc, mul_div_cancel₀]

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
#### A.3.1. Fourier multipliers
-/

/-- Send a function `f : Space d → E` to the function `f : Space d → Hom (WaveVectorSpace d, E)`
given by `x ↦ k ↦ b * I * (k ⬝ᵥ x) • f x`. This is designed so that the Fourier transform of
`fderivFourierIntegrand b f` is the `fderiv` of the Fourier transform of `f`. -/
noncomputable def fderivFourierIntegrand (f : Space d → E) (x : Space d) :
    WaveVectorSpace d →L[ℝ] E :=
  (b * I) • x.dual.smulRight (f x)

/-- Send a function `g : WaveVectorSpace d → E` to the function
`g : WaveVectorSpace d → Hom (Space d, E)` given by `k ↦ x ↦ -b * I * (k ⬝ᵥ x) • g k`.
This is designed so that the inverse Fourier transform of `fderivFourierInvIntegrand b g`
is the `fderiv` of the inverse Fourier transform of `g`. -/
noncomputable def fderivFourierInvIntegrand (g : WaveVectorSpace d → E) (k : WaveVectorSpace d) :
    Space d →L[ℝ] E :=
  -(b * I) • k.dual.smulRight (g k)

lemma fderivFourierIntegrand_eq (f : Space d → E) :
    fderivFourierIntegrand b f = fun x ↦ (b * I) • x.dual.smulRight (f x) :=
  rfl

lemma fderivFourierInvIntegrand_eq (g : WaveVectorSpace d → E) :
    fderivFourierInvIntegrand b g = fun k ↦ -(b * I) • k.dual.smulRight (g k) :=
  rfl

@[simp]
lemma fderivFourierIntegrand_apply (f : Space d → E) (x : Space d) (k : WaveVectorSpace d) :
    fderivFourierIntegrand b f x k = (b * I) • (k ⬝ᵥ x) • f x :=
  rfl

@[simp]
lemma fderivFourierInvIntegrand_apply
    (g : WaveVectorSpace d → E) (k : WaveVectorSpace d) (x : Space d) :
    fderivFourierInvIntegrand b g k x = -(b * I) • (k ⬝ᵥ x) • g k :=
  rfl

@[simp]
lemma opNorm_fderivFourierIntegrand (f : Space d → E) (x : Space d) :
    ‖fderivFourierIntegrand b f x‖ = |b| * ‖x‖ * ‖f x‖ := by
  simp [fderivFourierIntegrand_eq, norm_smul, mul_assoc]

@[simp]
lemma opNorm_fderivFourierInvIntegrand (g : WaveVectorSpace d → E) (k : WaveVectorSpace d) :
    ‖fderivFourierInvIntegrand b g k‖ = |b| * ‖k‖ * ‖g k‖ := by
  simp [fderivFourierInvIntegrand_eq, norm_smul, mul_assoc]

@[fun_prop]
lemma aestronglyMeasurable_fderivFourierIntegrand {f : Space d → E} (hf : AEStronglyMeasurable f) :
    AEStronglyMeasurable (fderivFourierIntegrand b f) := by
  rw [fderivFourierIntegrand_eq]
  fun_prop

@[fun_prop]
lemma aestronglyMeasurable_fderivFourierInvIntegrand
    {g : WaveVectorSpace d → E} (hg : AEStronglyMeasurable g) :
    AEStronglyMeasurable (fderivFourierInvIntegrand b g) := by
  rw [fderivFourierInvIntegrand_eq]
  fun_prop

lemma integrable_fderivFourierIntegrand {f : Space d → E}
    (hf : AEStronglyMeasurable f) (hf' : Integrable fun x ↦ ‖x‖ * ‖f x‖) :
    Integrable (fderivFourierIntegrand b f) :=
  hf'.smul |b| |>.mono (by fun_prop) <| ae_of_all _ <| by simp [mul_assoc]

lemma integrable_fderivFourierInvIntegrand {g : WaveVectorSpace d → E}
    (hg : AEStronglyMeasurable g) (hg' : Integrable fun k ↦ ‖k‖ * ‖g k‖) :
    Integrable (fderivFourierInvIntegrand b g) :=
  hg'.smul |b| |>.mono (by fun_prop) <| ae_of_all _ <| by simp [mul_assoc]

/-!
#### A.3.2. Fréchet derivatives
-/

lemma fderiv_fourierIntegral
    {f : Space d → E} (hf : Integrable f) (hf' : Integrable fun x ↦ ‖x‖ * ‖f x‖) :
    fderiv ℝ (fourierIntegral a b f) = fourierIntegral a b (fderivFourierIntegrand b f) := by
  rw [fourierIntegral_def, fderiv_const_smul_field, VectorFourier.fderiv_fourierIntegral _ hf hf']
  congr with x k
  calc
    _ = (2 * π * I * (b / (2 * π) * pairingCLM k x)) • f x := by simp [← coe_smul, smul_smul]
    _ = (b * I * pairingCLM k x) • f x := by field_simp
    _ = (b * I) • (k ⬝ᵥ x) • f x := by simp [← coe_smul, smul_smul]

lemma fderiv_fourierIntegralInv
    {g : WaveVectorSpace d → E} (hg : Integrable g) (hg' : Integrable (fun k ↦ ‖k‖ * ‖g k‖)) :
    fderiv ℝ (fourierIntegralInv a b g)
      = fourierIntegralInv a b (fderivFourierInvIntegrand b g) := by
  rw [fourierIntegralInv_def, fderiv_const_smul_field,
    VectorFourier.fderiv_fourierIntegral _ hg hg']
  congr with k x
  calc
    _ = -(2 * π * I * (b / (2 * π) * pairingCLM k x)) • g k := by simp [← coe_smul, smul_smul]
    _ = -(b * I * pairingCLM k x) • g k := by field_simp
    _ = -(b * I) • (k ⬝ᵥ x) • g k := by simp [← coe_smul, smul_smul]

/-!
#### A.3.3. Partial derivatives
-/

/-- The partial derivative of the Fourier transform of `f` along coordinate `i`
is the Fourier transform of `x ↦ (b * I * x i) • f x`, provided both integrals exist. -/
lemma deriv_fourierIntegral (i : Fin d)
    {f : Space d → E} (hf : Integrable f) (hf' : Integrable fun x ↦ ‖x‖ * ‖f x‖) :
    ∂[i] (fourierIntegral a b f) = fourierIntegral a b fun x ↦ (b * I * x i) • f x := by
  ext
  simp only [deriv_eq, hf, hf', fderiv_fourierIntegral, hf.aestronglyMeasurable,
    integrable_fderivFourierIntegrand, fourierIntegral_continuousLinearMap_apply]
  congr
  simp [dotProduct, ← nsmul_eq_mul, ← coe_smul, smul_smul]

/-- The partial derivative of the inverse Fourier transform of `g` along coordinate `i`
is the inverse Fourier transform of `k ↦ (-b * I * k i) • g k`, provided both integrals exist. -/
lemma deriv_fourierIntegralInv (i : Fin d)
    {g : WaveVectorSpace d → E} (hg : Integrable g) (hg' : Integrable fun k ↦ ‖k‖ * ‖g k‖) :
    ∂[i] (fourierIntegralInv a b g) = fourierIntegralInv a b fun k ↦ -(b * I * k i) • g k := by
  ext
  simp only [Space.deriv_eq, hg, hg', fderiv_fourierIntegralInv, hg.aestronglyMeasurable,
    integrable_fderivFourierInvIntegrand, fourierIntegralInv_continuousLinearMap_apply]
  congr
  simp [dotProduct, Space.basis_apply, ← coe_smul, smul_smul]

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
\tilde{f}(k) := \frac{1}{\sqrt{2\pi}} \int f(x)\,\mathrm{e}^{\mathrm{i}k\cdot x} \,\mathrm{d}x
\;,\qquad
f(x) := \frac{1}{\sqrt{2\pi}} \int \tilde{f}(k)\,\mathrm{e}^{-\mathrm{i}k\cdot x} \,\mathrm{d}k
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
f(x) := \frac{1}{2\pi} \int \tilde{f}(k)\,\mathrm{e}^{\mathrm{i}k\cdot x} \,\mathrm{d}k
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
