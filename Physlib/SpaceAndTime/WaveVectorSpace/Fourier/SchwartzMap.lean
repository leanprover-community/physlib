/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Physlib.SpaceAndTime.WaveVectorSpace.Fourier.Basic
/-!

# Fourier transforms between `𝓢(Space d, E)` and `𝓢(WaveVectorSpace d, E)`

## i. Overview

## ii. Key results

## iii. Table of contents

- A. Fourier transforms
  - A.1. As continuous linear maps

## iv. References

-/

@[expose] public section

variable {d : ℕ}

namespace WaveVectorSpace

/-!
## A. Fourier transforms
-/

noncomputable section Schwartz

open MeasureTheory SchwartzMap
open scoped FourierTransform Real

local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

variable (a : ℝ) (b : ℝˣ)
  (𝕜 : Type*) [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace 𝕜 E] [SMulCommClass ℂ 𝕜 E]
  (f : 𝓢(Space d, E)) (g : 𝓢(WaveVectorSpace d, E)) (x : Space d) (k : WaveVectorSpace d)

/-!
### A.1. As continuous linear maps
-/

/-- The Fourier transform between Schwartz spaces as a continuous linear map. -/
def fourierTransformCLM : 𝓢(Space d, E) →L[𝕜] 𝓢(WaveVectorSpace d, E) :=
  let c : ℝˣ := .mk (-(b / (2 * π))) (-(2 * π / b)) (by norm_num) (by norm_num)
  (|b.val| / (2 * π) ^ (1 - a)) ^ (d / 2 : ℝ)
    • compCLMOfContinuousLinearEquiv 𝕜 (basis.repr.toContinuousLinearEquiv.trans <| .smulLeft c)
      ∘L FourierTransform.fourierCLM 𝕜 𝓢(ℝᵈ, E)
      ∘L compCLMOfContinuousLinearEquiv 𝕜 Space.basis.repr.toContinuousLinearEquiv.symm

lemma coe_fourierTransformCLM : fourierTransformCLM a b 𝕜 f = fourierIntegral a b f := by
  ext
  simp [fourierTransformCLM, fourierIntegral_eq_smul_fourier_comp, fourier_coe]

lemma fourierTransformCLM_apply : fourierTransformCLM a b 𝕜 f k = fourierIntegral a b f k :=
  congrFun (coe_fourierTransformCLM a b 𝕜 f) k

/-- The inverse Fourier transform between Schwartz spaces as a continuous linear map. -/
def fourierTransformInvCLM : 𝓢(WaveVectorSpace d, E) →L[𝕜] 𝓢(Space d, E) :=
  let c : ℝˣ := .mk (-(b / (2 * π))) (-(2 * π / b)) (by norm_num) (by norm_num)
  (|b.val| / (2 * π) ^ (1 + a)) ^ (d / 2 : ℝ)
    • compCLMOfContinuousLinearEquiv 𝕜
        (Space.basis.repr.toContinuousLinearEquiv.trans <| .smulLeft c)
      ∘L FourierTransform.fourierInvCLM 𝕜 𝓢(ℝᵈ, E)
      ∘L compCLMOfContinuousLinearEquiv 𝕜 basis.repr.toContinuousLinearEquiv.symm

lemma coe_fourierTransformInvCLM : fourierTransformInvCLM a b 𝕜 g = fourierIntegralInv a b g := by
  ext
  simp [fourierTransformInvCLM, fourierIntegralInv_eq_smul_fourierInv_comp, fourierInv_coe]

lemma fourierTransformInvCLM_apply :
    fourierTransformInvCLM a b 𝕜 g x = fourierIntegralInv a b g x :=
  congrFun (coe_fourierTransformInvCLM a b 𝕜 g) x

end Schwartz

end WaveVectorSpace
