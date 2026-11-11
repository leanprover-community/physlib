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

## ii. Key results

## iii. Table of contents

## iv. References

-/

@[expose] public section

variable {d : ℕ}

namespace WaveVectorSpace

/-!
## A. Fourier integrals
-/

open MeasureTheory VectorFourier
open scoped Real

variable (a b : ℝ) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

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

lemma physFourier_eq (f : Space d → E) :
    physFourier a b f
      = √(|b| / (2 * π) ^ (1 - a))
        • fourierIntegral (physChar b) volume (-pairingCLM.flip.toLinearMap₁₂) f :=
  rfl

/-- The inverse Fourier integral over `WaveVectorSpace`,

`√(|b| / (2 * π) ^ (1 + a)) • ∫ k, exp (-b * (k ⬝ᵥ x) * I) • g k ∂volume`,

parametrized by `a b : ℝ`.
-/
noncomputable def physFourierInv (g : WaveVectorSpace d → E) (x : Space d) : E :=
  √(|b| / (2 * π) ^ (1 + a)) • fourierIntegral (physChar b) volume pairingCLM.toLinearMap₁₂ g x

lemma physFourierInv_eq (g : WaveVectorSpace d → E) :
    physFourierInv a b g
      = √(|b| / (2 * π) ^ (1 + a))
        • fourierIntegral (physChar b) volume pairingCLM.toLinearMap₁₂ g :=
  rfl

end WaveVectorSpace
