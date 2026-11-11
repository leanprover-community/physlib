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

The two main definitions are `physFourier a b : (Space d → E) → WaveVectorSpace d → E`
and `physFourierInv a b : (WaveVectorSpace d → E) → Space d → E` which amount to the following
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
and most results require that input function be integrable.

Results which hold for all `a` and `b` should be written in terms of `physFourier a b`.
To select a particular convention, include the line `open scoped Fourier_[a]_[b]`
(*e.g.* `open scoped Fourier_1_n1` for $(a,b) = (1,-1)$) and use the notation `𝓕` and `𝓕⁻`.
If a common convention is missing it can be added below in section B.

## ii. Key results

- `physFourier a b` : the Fourier integral with real parameters `a` and `b`,
  corresponding to a choice of convention, which maps a function `f : Space d → E`
  to its Fourier transform of type `WaveVectorSpace d → E`.
- `physFourierInv a b` : the inverse Fourier integral with real parameters `a` and `b`,
  corresponding to a choice of convention, which maps a function `g : WaveVectorSpace d → E`
  to its Fourier transform of type `Space d → E`.

## iii. Table of contents

- A. Fourier integrals
  - A.1. Two-parameter definitions
  - A.2. Basic properties
- B. Fourier instances for different conventions
  - B.1. `(a, b) = (0, 1)`
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

section PhysFourier

open MeasureTheory VectorFourier
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
noncomputable def physFourier (f : Space d → E) (k : WaveVectorSpace d) : E :=
  √(|b| / (2 * π) ^ (1 - a))
    • fourierIntegral (physChar b) volume (-pairingCLM.flip.toLinearMap₁₂) f k

lemma physFourier_def (f : Space d → E) :
    physFourier a b f
      = √(|b| / (2 * π) ^ (1 - a))
        • fourierIntegral (physChar b) volume (-pairingCLM.flip.toLinearMap₁₂) f :=
  rfl

open Complex in
lemma physFourier_eq (f : Space d → E) (k : WaveVectorSpace d) :
    physFourier a b f k
      = √(|b| / (2 * π) ^ (1 - a)) • ∫ x : Space d, cexp (b * (k ⬝ᵥ x) * I) • f x := by
  simp [physFourier_def, fourierIntegral, physChar, pairingCLM_apply_eq_dual, dual_apply,
    Circle.smul_def]

/-- The inverse Fourier integral over `WaveVectorSpace`,

`√(|b| / (2 * π) ^ (1 + a)) • ∫ k, exp (-b * (k ⬝ᵥ x) * I) • g k ∂volume`,

parametrized by `a b : ℝ`.
-/
noncomputable def physFourierInv (g : WaveVectorSpace d → E) (x : Space d) : E :=
  √(|b| / (2 * π) ^ (1 + a)) • fourierIntegral (physChar b) volume pairingCLM.toLinearMap₁₂ g x

lemma physFourierInv_def (g : WaveVectorSpace d → E) :
    physFourierInv a b g
      = √(|b| / (2 * π) ^ (1 + a))
        • fourierIntegral (physChar b) volume pairingCLM.toLinearMap₁₂ g :=
  rfl

open Complex in
lemma physFourierInv_eq (g : WaveVectorSpace d → E) (x : Space d) :
    physFourierInv a b g x
      = √(|b| / (2 * π) ^ (1 + a)) • ∫ k : WaveVectorSpace d, cexp (-b * (k ⬝ᵥ x) * I) • g k := by
  simp [physFourierInv_def, fourierIntegral, physChar, pairingCLM_apply_eq_dual, dual_apply,
    Circle.smul_def, Complex.exp_neg]

/-!
### A.2. Basic properties
-/

lemma physFourier_congr_ae {f₁ f₂ : Space d → E} (hf : f₁ =ᵐ[volume] f₂) :
    physFourier a b f₁ = physFourier a b f₂ := by
  rw [physFourier_def, physFourier_def, fourierIntegral_congr_ae _ _ _ hf]

lemma physFourierInv_congr_ae {g₁ g₂ : WaveVectorSpace d → E} (hg : g₁ =ᵐ[volume] g₂) :
    physFourierInv a b g₁ = physFourierInv a b g₂ := by
  rw [physFourierInv_def, physFourierInv_def, fourierIntegral_congr_ae _ _ _ hg]

lemma physFourier_const_smul (f : Space d → E) (c : ℂ) :
    physFourier a b (c • f) = c • physFourier a b f := by
  simp only [physFourier_def, fourierIntegral_const_smul, smul_comm c]

lemma physFourierInv_const_smul (f : WaveVectorSpace d → E) (c : ℂ) :
    physFourierInv a b (c • f) = c • physFourierInv a b f := by
  simp only [physFourierInv_def, fourierIntegral_const_smul, smul_comm c]

lemma physFourier_add {f₁ f₂ : Space d → E} (hf₁ : Integrable f₁) (hf₂ : Integrable f₂) :
    physFourier a b (f₁ + f₂) = physFourier a b f₁ + physFourier a b f₂ := by
  repeat rw [physFourier_def]
  rw [← smul_add, fourierIntegral_add physChar_continuous pairingCLM.flip.continuous₂.neg hf₁ hf₂]

lemma physFourierInv_add
    {g₁ g₂ : WaveVectorSpace d → E} (hg₁ : Integrable g₁) (hg₂ : Integrable g₂) :
    physFourierInv a b (g₁ + g₂) = physFourierInv a b g₁ + physFourierInv a b g₂ := by
  repeat rw [physFourierInv_def]
  rw [← smul_add, fourierIntegral_add physChar_continuous pairingCLM.continuous₂ hg₁ hg₂]

lemma physFourier_continuous {f : Space d → E} (hf : Integrable f) :
    Continuous (physFourier a b f) :=
  (fourierIntegral_continuous physChar_continuous pairingCLM.flip.continuous₂.neg hf).const_smul _

lemma physFourierInv_continuous {g : WaveVectorSpace d → E} (hg : Integrable g) :
    Continuous (physFourierInv a b g) :=
  (fourierIntegral_continuous physChar_continuous pairingCLM.continuous₂ hg).const_smul _

end PhysFourier

/-!
## B. Fourier instances for different conventions
-/

section Conventions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-!
### B.1. `(a, b) = (0, 1)`

$$
\tilde{f}(k) := \frac{1}{\sqrt{2\pi}}\int f(x)\,\mathrm{e}^{\mathrm{i}k\cdot x} \,\mathrm{d}x
\;,\qquad
f(x) := \frac{1}{\sqrt{2\pi}}\int \tilde{f}(k)\,\mathrm{e}^{-\mathrm{i}k\cdot x} \,\mathrm{d}k
$$
-/

namespace Fourier_0_1

noncomputable scoped instance : FourierTransform (Space d → E) (WaveVectorSpace d → E) where
  fourier := physFourier 0 1

noncomputable scoped instance : FourierTransformInv (WaveVectorSpace d → E) (Space d → E) where
  fourierInv := physFourierInv 0 1

end Fourier_0_1

/-!
### B.2. `(a, b) = (1, -1)`

$$
\tilde{f}(k) := \int f(x)\,\mathrm{e}^{-\mathrm{i}k\cdot x} \,\mathrm{d}x
\;,\qquad
f(x) := \frac{1}{2\pi}\int \tilde{f}(k)\,\mathrm{e}^{\mathrm{i}k\cdot x} \,\mathrm{d}k
$$
-/

namespace Fourier_1_n1

noncomputable scoped instance : FourierTransform (Space d → E) (WaveVectorSpace d → E) where
  fourier := physFourier 1 (-1)

noncomputable scoped instance : FourierTransformInv (WaveVectorSpace d → E) (Space d → E) where
  fourierInv := physFourierInv 1 (-1)

end Fourier_1_n1

end Conventions

end WaveVectorSpace
