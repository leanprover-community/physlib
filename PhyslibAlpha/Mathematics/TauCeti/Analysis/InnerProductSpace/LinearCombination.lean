/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Comparing linear combinations by their Gram kernels

Two families with the same pairwise inner products give linear combinations of the same norm when
supplied with the same finitely supported coefficients.

## i. Overview

Two families with the same pairwise inner products give linear combinations of the same norm
when supplied with the same finitely supported coefficients. This comparison applies in
seminormed inner product spaces and is useful for comparing realizations of a positive-definite
kernel before constructing an isometry between their closed spans.

## ii. Key results

This file proves the statement described in the overview.

## iii. Table of contents

- A. Development

## iv. References

* Standard material; the statements and proofs are original to this formalization.
-/

public section

/-! ## A. Development -/

open InnerProductSpace

namespace Finsupp

variable {𝕜 α E F : Type*} [RCLike 𝕜]
  [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [SeminormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- Families with equal pairwise inner products give linear combinations of equal norm
for the same finitely supported coefficients. -/
lemma norm_linearCombination_eq_of_inner_eq (f : α →₀ 𝕜) {φ : α → E} {ψ : α → F}
    (h : ∀ a b, ⟪φ a, φ b⟫_𝕜 = ⟪ψ a, ψ b⟫_𝕜) :
    ‖linearCombination 𝕜 φ f‖ = ‖linearCombination 𝕜 ψ f‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← inner_self_eq_norm_sq (𝕜 := 𝕜), ← inner_self_eq_norm_sq (𝕜 := 𝕜)]
  congr 1
  simp only [linearCombination_apply, Finsupp.sum_inner, Finsupp.inner_sum,
    inner_smul_left, inner_smul_right, h]

end Finsupp
