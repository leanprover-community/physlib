/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
/-!

# Strict bounds on the square of the sine

This file may eventually be upstreamed to Mathlib.

## i. Overview

Mathlib bounds the square of the sine by `sin x ^ 2 ≤ 1` for every real `x` (`Real.sin_sq_le_one`),
with equality exactly at the odd multiples of `π / 2`. This file records the strict form of that
bound, `sin x ^ 2 < 1` on the open interval `|x| < π / 2`, where the cosine is positive and
`1 - sin² x = cos² x`, together with its half-angle form `sin (θ / 2) ^ 2 < 1` for `|θ| < π`.

Physlib uses the half-angle form for the simple pendulum: the parameter `sin² (θ₀ / 2)` of the
period formula lies in the domain `m < 1` of the complete elliptic integral `Real.completeEllipticK`
for every libration amplitude `|θ₀| < π`.

## ii. Key results

- `Real.sin_sq_lt_one` : `sin x ^ 2 < 1` for `|x| < π / 2`.
- `Real.sin_half_sq_lt_one` : `sin (θ / 2) ^ 2 < 1` for `|θ| < π`.

## iii. Table of contents

- A. Strict bounds on the square of the sine

## iv. References

* Landau & Lifshitz, Mechanics, 3rd ed., §11, Problem 1 (the pendulum period, whose parameter is
  `sin² (θ₀ / 2)`). [ref: landau_mechanics]
-/

@[expose] public section

namespace Real

/-!

## A. Strict bounds on the square of the sine

On `|x| < π / 2` the cosine is positive, so `1 - sin² x = cos² x` is positive; the half-angle form
follows by applying this at `x = θ / 2`.

-/

/-- `sin x ^ 2 < 1` for `|x| < π / 2`: the cosine is positive there, and `1 - sin² x = cos² x`. -/
lemma sin_sq_lt_one {x : ℝ} (h : |x| < π / 2) : sin x ^ 2 < 1 := by
  obtain ⟨h₁, h₂⟩ := abs_lt.1 h
  rw [← sub_pos, ← cos_sq']
  exact pow_pos (cos_pos_of_mem_Ioo ⟨by linarith, h₂⟩) 2

/-- The half-angle form of `sin_sq_lt_one`: `sin (θ / 2) ^ 2 < 1` for `|θ| < π`. For the pendulum
this says that the parameter `sin² (θ₀ / 2)` of the period formula lies in the domain of
`completeEllipticK` for every libration amplitude `|θ₀| < π`. -/
lemma sin_half_sq_lt_one {θ : ℝ} (h : |θ| < π) : sin (θ / 2) ^ 2 < 1 := by
  refine sin_sq_lt_one ?_
  rw [abs_div, abs_two]
  linarith [abs_nonneg θ]

end Real
