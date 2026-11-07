/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-!

# Pointwise polynomial decay of Schwartz functions

A Schwartz function decays faster than every power of `1 + ‖z‖`.

## i. Overview

The estimate `‖h z‖ ≤ 2ᵏ⁻¹ (p₀ h + pₖ h) (1 + ‖z‖)⁻ᵏ` follows from the binomial bound
`(1 + t)ᵏ ≤ 2ᵏ⁻¹ (1 + tᵏ)` and the two seminorms `p₀` and `pₖ`. The constant is a seminorm of
`h`. So it is uniform on bounded sets of Schwartz functions.

## ii. Key results

- `SchwartzMap.norm_le_rpow_neg_mul` : the pointwise decay with an explicit constant.
- `SchwartzMap.exists_norm_le_rpow_neg` : the decay with an unspecified constant.

## iii. Table of contents

- A. Decay

## iv. References

None.

## A. Decay

- `SchwartzMap.norm_le_rpow_neg_mul` : the pointwise decay with an explicit constant.
- `SchwartzMap.exists_norm_le_rpow_neg` : the decay with an unspecified constant.
-/

@[expose] public section

noncomputable section

open scoped SchwartzMap

namespace SchwartzMap

variable {V F : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F]
  [NormedSpace ℝ F] (𝕜 : Type*) [RCLike 𝕜] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]

/-- **Decay of a Schwartz function with an explicit constant.** -/
lemma norm_le_rpow_neg_mul (h : 𝓢(V, F)) (k : ℕ) (z : V) :
    ‖h z‖ ≤ 2 ^ (k - 1) * (SchwartzMap.seminorm 𝕜 0 0 h + SchwartzMap.seminorm 𝕜 k 0 h) *
      (1 + ‖z‖) ^ (-(k : ℝ)) := by
  have hpos : 0 < (1 + ‖z‖) ^ k := by positivity
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ hpos]
  have h2 := add_pow_le (zero_le_one' ℝ) (norm_nonneg z) k
  have h0 : ‖h z‖ ≤ SchwartzMap.seminorm 𝕜 0 0 h := by
    simpa using SchwartzMap.le_seminorm 𝕜 0 0 h z
  have h1 : ‖z‖ ^ k * ‖h z‖ ≤ SchwartzMap.seminorm 𝕜 k 0 h := by
    simpa using SchwartzMap.le_seminorm 𝕜 k 0 h z
  calc ‖h z‖ * (1 + ‖z‖) ^ k ≤ ‖h z‖ * (2 ^ (k - 1) * (1 ^ k + ‖z‖ ^ k)) :=
        mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    _ = 2 ^ (k - 1) * (‖h z‖ + ‖z‖ ^ k * ‖h z‖) := by ring
    _ ≤ 2 ^ (k - 1) * (SchwartzMap.seminorm 𝕜 0 0 h + SchwartzMap.seminorm 𝕜 k 0 h) := by
        gcongr

/-- A Schwartz function decays like `(1 + ‖z‖)⁻ᵏ` for every `k`. The constant is nonnegative. -/
lemma exists_norm_le_rpow_neg (h : 𝓢(V, F)) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : V, ‖h z‖ ≤ C * (1 + ‖z‖) ^ (-(k : ℝ)) :=
  ⟨2 ^ (k - 1) * (SchwartzMap.seminorm ℝ 0 0 h + SchwartzMap.seminorm ℝ k 0 h), by positivity,
    fun z => norm_le_rpow_neg_mul ℝ h k z⟩

end SchwartzMap
