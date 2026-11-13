/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Mathlib.Analysis.Fourier.FourierTransform
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

## iii. Table of contents

- A. Fourier integrals
  - A.1. Two-parameter definitions
  - A.2. Basic properties
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

open MeasureTheory
open scoped Real

variable (a b : ℝ) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-!
### A.1. Two-parameter definitions
-/

/-- The additive character `fun r ↦ exp (b * r * I)` from `ℝ` to the unit circle in `ℂ`. -/
noncomputable def physChar : AddChar ℝ Circle where
  toFun r := Circle.exp (b * r)
  map_zero_eq_one' := by rw [mul_zero, Circle.exp_zero]
  map_add_eq_mul' _ _ := by rw [mul_add, Circle.exp_add]

variable {b} in
@[fun_prop]
lemma physChar_continuous : Continuous (physChar b) := by
  rw [AddChar.coe_mk]
  fun_prop

/-- The Fourier integral over `Space`,

`√(|b| / (2 * π) ^ (1 - a)) • ∫ x, exp (b * (k ⬝ᵥ x) * I) • f x ∂volume`,

parametrized by `a b : ℝ`.
-/
noncomputable def fourierIntegral (f : Space d → E) (k : WaveVectorSpace d) : E :=
  √(|b| / (2 * π) ^ (1 - a))
    • VectorFourier.fourierIntegral (physChar b) volume (-pairingCLM.flip.toLinearMap₁₂) f k

lemma fourierIntegral_def (f : Space d → E) :
    fourierIntegral a b f
      = √(|b| / (2 * π) ^ (1 - a))
        • VectorFourier.fourierIntegral (physChar b) volume (-pairingCLM.flip.toLinearMap₁₂) f :=
  rfl

open Complex in
lemma fourierIntegral_eq (f : Space d → E) (k : WaveVectorSpace d) :
    fourierIntegral a b f k
      = √(|b| / (2 * π) ^ (1 - a)) • ∫ x : Space d, cexp (b * (k ⬝ᵥ x) * I) • f x := by
  simp [fourierIntegral_def, VectorFourier.fourierIntegral, physChar, pairingCLM_apply_eq_dual,
    dual_apply, Circle.smul_def]

/-- The inverse Fourier integral over `WaveVectorSpace`,

`√(|b| / (2 * π) ^ (1 + a)) • ∫ k, exp (-b * (k ⬝ᵥ x) * I) • g k ∂volume`,

parametrized by `a b : ℝ`.
-/
noncomputable def fourierIntegralInv (g : WaveVectorSpace d → E) (x : Space d) : E :=
  √(|b| / (2 * π) ^ (1 + a))
    • VectorFourier.fourierIntegral (physChar b) volume pairingCLM.toLinearMap₁₂ g x

lemma fourierIntegralInv_def (g : WaveVectorSpace d → E) :
    fourierIntegralInv a b g
      = √(|b| / (2 * π) ^ (1 + a))
        • VectorFourier.fourierIntegral (physChar b) volume pairingCLM.toLinearMap₁₂ g :=
  rfl

open Complex in
lemma fourierIntegralInv_eq (g : WaveVectorSpace d → E) (x : Space d) :
    fourierIntegralInv a b g x
      = √(|b| / (2 * π) ^ (1 + a)) • ∫ k : WaveVectorSpace d, cexp (-b * (k ⬝ᵥ x) * I) • g k := by
  simp [fourierIntegralInv_def, VectorFourier.fourierIntegral, physChar, pairingCLM_apply_eq_dual,
    dual_apply, Circle.smul_def, Complex.exp_neg]

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

lemma fourierIntegral_const_smul (f : Space d → E) (c : ℂ) :
    fourierIntegral a b (c • f) = c • fourierIntegral a b f := by
  simp only [fourierIntegral_def, VectorFourier.fourierIntegral_const_smul, smul_comm c]

lemma fourierIntegralInv_const_smul (f : WaveVectorSpace d → E) (c : ℂ) :
    fourierIntegralInv a b (c • f) = c • fourierIntegralInv a b f := by
  simp only [fourierIntegralInv_def, VectorFourier.fourierIntegral_const_smul, smul_comm c]

lemma fourierIntegral_add {f₁ f₂ : Space d → E} (hf₁ : Integrable f₁) (hf₂ : Integrable f₂) :
    fourierIntegral a b (f₁ + f₂) = fourierIntegral a b f₁ + fourierIntegral a b f₂ := by
  rw [fourierIntegral_def, fourierIntegral_def, fourierIntegral_def, ← smul_add,
    VectorFourier.fourierIntegral_add physChar_continuous pairingCLM.flip.continuous₂.neg hf₁ hf₂]

lemma fourierIntegralInv_add
    {g₁ g₂ : WaveVectorSpace d → E} (hg₁ : Integrable g₁) (hg₂ : Integrable g₂) :
    fourierIntegralInv a b (g₁ + g₂) = fourierIntegralInv a b g₁ + fourierIntegralInv a b g₂ := by
  rw [fourierIntegralInv_def, fourierIntegralInv_def, fourierIntegralInv_def, ← smul_add,
    VectorFourier.fourierIntegral_add physChar_continuous pairingCLM.continuous₂ hg₁ hg₂]

lemma fourierIntegral_continuous {f : Space d → E} (hf : Integrable f) :
    Continuous (fourierIntegral a b f) :=
  VectorFourier.fourierIntegral_continuous physChar_continuous pairingCLM.flip.continuous₂.neg hf
    |>.const_smul _

lemma fourierIntegralInv_continuous {g : WaveVectorSpace d → E} (hg : Integrable g) :
    Continuous (fourierIntegralInv a b g) :=
  VectorFourier.fourierIntegral_continuous physChar_continuous pairingCLM.continuous₂ hg
    |>.const_smul _

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
