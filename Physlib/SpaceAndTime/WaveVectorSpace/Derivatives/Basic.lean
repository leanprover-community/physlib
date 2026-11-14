/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Physlib.SpaceAndTime.WaveVectorSpace.Basic
/-!

# Derivatives on `WaveVectorSpace`

## i. Overview

## ii. Key results

## iii. Table of contents

- A. Derivatives of functions on `WaveVectorSpace d`
  - A.1. Constant functions
  - A.2. Addition and subtraction
  - A.3. Scalar multiplication

## iv. References

-/
@[expose] public section

namespace WaveVectorSpace

variable {d : ℕ}

/-!
## A. Derivatives of functions on `WaveVectorSpace d`
-/

/-- Given a function `f : WaveVectorSpace d → M`,
`∂[i] f` is its derivative in the direction of the `i`ᵗʰ basis vector. -/
noncomputable def deriv {M : Type*} [AddCommGroup M] [Module ℝ M] [TopologicalSpace M]
    (i : Fin d) (f : WaveVectorSpace d → M) (k : WaveVectorSpace d) : M :=
  fderiv ℝ f k (basis i)

@[inherit_doc deriv]
notation "∂[" i "]" => deriv i

lemma deriv_eq {M : Type*} [AddCommGroup M] [Module ℝ M] [TopologicalSpace M]
    (i : Fin d) (f : WaveVectorSpace d → M) (k : WaveVectorSpace d) :
    ∂[i] f k = fderiv ℝ f k (basis i) :=
  rfl

/-!
### A.1. Constant functions
-/

@[simp]
lemma deriv_const
    {M : Type*} [AddCommGroup M] [Module ℝ M] [TopologicalSpace M] (i : Fin d) (m : M) :
    ∂[i] (fun _ : WaveVectorSpace d ↦ m) = 0 := by
  ext
  simp [deriv_eq]

/-!
### A.2. Addition and subtraction
-/

section AddSub

variable {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]
  (i : Fin d) {f₁ f₂ : WaveVectorSpace d → M} {k : WaveVectorSpace d}
  (hf₁ : DifferentiableAt ℝ f₁ k) (hf₂ : DifferentiableAt ℝ f₂ k)

include hf₁ hf₂

@[to_fun deriv_fun_add]
lemma deriv_add : ∂[i] (f₁ + f₂) k = ∂[i] f₁ k + ∂[i] f₂ k := by simp [deriv_eq, fderiv_add hf₁ hf₂]

@[to_fun deriv_fun_sub]
lemma deriv_sub : ∂[i] (f₁ - f₂) k = ∂[i] f₁ k - ∂[i] f₂ k := by simp [deriv_eq, fderiv_sub hf₁ hf₂]

end AddSub

/-!
### A.3. Scalar multiplication
-/

section SMul

variable {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]

@[to_fun deriv_fun_smul]
lemma deriv_smul {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜] [NormedSpace 𝕜 M]
    (i : Fin d) {c : WaveVectorSpace d → 𝕜} {f : WaveVectorSpace d → M} {k : WaveVectorSpace d}
    (hc : DifferentiableAt ℝ c k) (hf : DifferentiableAt ℝ f k) :
    ∂[i] (c • f) k = c k • ∂[i] f k + ∂[i] c k • f k := by
  simp [deriv_eq, fderiv_smul hc hf]

@[to_fun deriv_fun_const_smul]
lemma deriv_const_smul
    {R : Type*} [Semiring R] [Module R M] [SMulCommClass ℝ R M] [ContinuousConstSMul R M] (c : R)
    (i : Fin d) {f : WaveVectorSpace d → M} {k : WaveVectorSpace d} (hf : DifferentiableAt ℝ f k) :
    ∂[i] (c • f) k = c • ∂[i] f k := by
  simp [deriv_eq, fderiv_const_smul hf]

end SMul

end WaveVectorSpace
