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

In this module are defined the Fourier transforms between the Schwartz spaces `𝓢(Space d, E)`
and `𝓢(WaveVectorSpace d, E)`. These depend on two parameters `a : ℝ` and `b : ℝˣ` so as to agree
with `fourierIntegral` and `fourierIntegralInv`.

## ii. Key results

- `fourierTransformCLM` : The Fourier transform on Schwartz spaces as a continuous linear map,
  depending on two parameters `a : ℝ` and `b : ℝˣ`.
- `fourierTransformInvCLM` : The inverse Fourier transform on Schwartz spaces as a continuous
  linear map, depending on two parameters `a : ℝ` and `b : ℝˣ`.
- `coe_fourierTransformCLM`/`coe_fourierTransformInvCLM` : The Fourier transform of a Schwartz map
  agrees with the Fourier integral of its coercion to a function, and similarly for the inverse
  Fourier transform. In particular, the parametrizations in terms of `a` and `b` are the same.
- `fourierTransformInvCLM_fourierTransformCLM_eq`/`fourierTransformCLM_fourierTransformInvCLM_eq` :
  The Fourier inversion formulae for `fourierTransformCLM` and `fourierTransformInvCLM`.
- `fourierTransformCLE` : The Fourier transform and its inverse between the Schwartz spaces
  `𝓢(Space d, E)` and `𝓢(WaveVectorSpace d, E)` bundled as a continuous linear equivalence
  when `E` is a complete space.

## iii. Table of contents

- A. Fourier transforms
  - A.1. As continuous linear maps
  - A.2. Basic properties
  - A.3. Inversion
  - A.4. As a continuous linear equivalence

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

/-!
### A.2. Basic properties

Basic properties about (inverse) Fourier integrals of Schwartz maps
can be inferred from `coe_fourierTransformCLM` and `coe_fourierTransfromInvCLM`.
-/

section

include 𝕜

lemma continuous_fourierIntegral_coe : Continuous (fourierIntegral a b f) :=
  coe_fourierTransformCLM a b 𝕜 f ▸ (fourierTransformCLM a b 𝕜 f).continuous

lemma continuous_fourierIntegralInv_coe : Continuous (fourierIntegralInv a b g) :=
  coe_fourierTransformInvCLM a b 𝕜 g ▸ (fourierTransformInvCLM a b 𝕜 g).continuous

lemma differentiable_fourierIntegral_coe : Differentiable ℝ (fourierIntegral a b f) :=
  coe_fourierTransformCLM a b 𝕜 f ▸ (fourierTransformCLM a b 𝕜 f).differentiable

lemma differentiable_fourierIntegralInv_coe : Differentiable ℝ (fourierIntegralInv a b g) :=
  coe_fourierTransformInvCLM a b 𝕜 g ▸ (fourierTransformInvCLM a b 𝕜 g).differentiable

lemma smooth_fourierIntegral_coe (n : ℕ∞) : ContDiff ℝ n (fourierIntegral a b f) :=
  coe_fourierTransformCLM a b 𝕜 f ▸ (fourierTransformCLM a b 𝕜 f).smooth n

lemma smooth_fourierIntegralInv_coe (n : ℕ∞) : ContDiff ℝ n (fourierIntegralInv a b g) :=
  coe_fourierTransformInvCLM a b 𝕜 g ▸ (fourierTransformInvCLM a b 𝕜 g).smooth n

lemma integrable_fourierIntegral_coe : Integrable (fourierIntegral a b f) :=
  coe_fourierTransformCLM a b 𝕜 f ▸ (fourierTransformCLM a b 𝕜 f).integrable

lemma integrable_fourierIntegralInv_coe : Integrable (fourierIntegralInv a b g) :=
  coe_fourierTransformInvCLM a b 𝕜 g ▸ (fourierTransformInvCLM a b 𝕜 g).integrable

lemma integrable_pow_mul_fourierIntegral_coe (n : ℕ) :
    Integrable (fun k ↦ ‖k‖ ^ n * ‖fourierIntegral a b f k‖) :=
  coe_fourierTransformCLM a b 𝕜 f ▸ (fourierTransformCLM a b 𝕜 f).integrable_pow_mul _ n

lemma integrable_pow_mul_fourierIntegralInv_coe (n : ℕ) :
    Integrable (fun x ↦ ‖x‖ ^ n * ‖fourierIntegralInv a b g x‖) :=
  coe_fourierTransformInvCLM a b 𝕜 g ▸ (fourierTransformInvCLM a b 𝕜 g).integrable_pow_mul _ n

end

/-!
### A.3. Inversion
-/

/-- The Fourier inversion formula: `𝓕⁻ (𝓕 f) = f` for `f : 𝓢(Space d, E)`. -/
@[simp]
lemma fourierTransformInvCLM_fourierTransformCLM_eq [CompleteSpace E] :
    fourierTransformInvCLM a b 𝕜 (fourierTransformCLM a b 𝕜 f) = f := by
  ext
  simp [fourierTransformInvCLM_apply, coe_fourierTransformCLM, f.continuous, f.integrable,
    fourierIntegralInv_fourierIntegral_eq, integrable_fourierIntegral_coe a b 𝕜]

/-- The Fourier inversion formula: `𝓕 (𝓕⁻ g) = g` for `g : 𝓢(WaveVectorSpace d, E)`. -/
@[simp]
lemma fourierTransformCLM_fourierTransformInvCLM_eq [CompleteSpace E] :
    fourierTransformCLM a b 𝕜 (fourierTransformInvCLM a b 𝕜 g) = g := by
  ext
  simp [fourierTransformCLM_apply, coe_fourierTransformInvCLM, g.continuous, g.integrable,
    fourierIntegral_fourierIntegralInv_eq, integrable_fourierIntegralInv_coe a b 𝕜]

/-!
### A.4. As a continuous linear equivalence
-/

section CLE

variable [CompleteSpace E]

/-- The Fourier transform between Schwartz spaces as a continuous linear equivalence. -/
def fourierTransformCLE : 𝓢(Space d, E) ≃L[𝕜] 𝓢(WaveVectorSpace d, E) :=
  .equivOfInverse'
    (fourierTransformCLM a b 𝕜) (fourierTransformInvCLM a b 𝕜) (by ext; simp) (by ext; simp)

lemma fourierTransformCLE_apply : fourierTransformCLE a b 𝕜 f = fourierTransformCLM a b 𝕜 f := rfl

lemma fourierTransformCLE_symm_apply :
    (fourierTransformCLE a b 𝕜).symm g = fourierTransformInvCLM a b 𝕜 g := rfl

end CLE

end Schwartz

end WaveVectorSpace
