/-
Copyright (c) 2026 Daniel Leonforte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Leonforte
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
/-!
# Positive semi-definite bilinear forms: zero-length vectors and Cauchy-Schwarz

## i. Overview

For a positive semi-definite symmetric bilinear form `B` on a module over an ordered field, a
vector `x` with `B x x = 0` is `B`-orthogonal to every vector, and `B` satisfies the
Cauchy-Schwarz inequality `B x y ^ 2 ≤ B x x * B y y`. Both follow from the nonnegativity of
`B (y - t • x) (y - t • x)` for a suitable scalar `t`.

## ii. Key results

- `LinearMap.BilinForm.IsPosSemidef.apply_eq_zero_of_apply_self_eq_zero` : a vector of zero
  `B`-length is `B`-orthogonal to every vector.
- `LinearMap.BilinForm.IsPosSemidef.apply_sq_le_apply_self_mul_apply_self` : the Cauchy-Schwarz
  inequality.

## iii. Table of contents

- A. Vectors of zero length
- B. The Cauchy-Schwarz inequality

## iv. References

- None.
-/

@[expose] public section

namespace LinearMap.BilinForm

variable {𝕜 M : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup M]
  [Module 𝕜 M] {B : LinearMap.BilinForm 𝕜 M}

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- The value of a symmetric bilinear form on `y - t • x` with itself. -/
lemma IsSymm.apply_sub_smul_self (hB : B.IsSymm) (x y : M) (t : 𝕜) :
    B (y - t • x) (y - t • x) = B y y - 2 * t * B x y + t ^ 2 * B x x := by
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
    hB.eq y x]
  ring

/-!

## A. Vectors of zero length

-/

/-- For a positive semi-definite bilinear form, a vector `x` with `B x x = 0` satisfies
`B x y = 0` for every `y`. -/
lemma IsPosSemidef.apply_eq_zero_of_apply_self_eq_zero (hB : B.IsPosSemidef) {x : M}
    (hx : B x x = 0) (y : M) : B x y = 0 := by
  by_contra hne
  have h := hB.isNonneg.nonneg (y - ((B y y + 1) / (2 * B x y)) • x)
  rw [hB.isSymm.apply_sub_smul_self, hx] at h
  have h1 : 2 * ((B y y + 1) / (2 * B x y)) * B x y = B y y + 1 := by
    field_simp
  linarith

/-!

## B. The Cauchy-Schwarz inequality

-/

/-- The **Cauchy-Schwarz inequality** for a positive semi-definite bilinear form:
`B x y ^ 2 ≤ B x x * B y y`. -/
lemma IsPosSemidef.apply_sq_le_apply_self_mul_apply_self (hB : B.IsPosSemidef) (x y : M) :
    B x y ^ 2 ≤ B x x * B y y := by
  rcases (hB.isNonneg.nonneg x).eq_or_lt with h0 | hpos
  · rw [hB.apply_eq_zero_of_apply_self_eq_zero h0.symm y, ← h0]
    simp
  · have h := hB.isNonneg.nonneg (y - (B x y / B x x) • x)
    rw [hB.isSymm.apply_sub_smul_self] at h
    have h1 : B y y - 2 * (B x y / B x x) * B x y + (B x y / B x x) ^ 2 * B x x =
        B y y - B x y ^ 2 / B x x := by
      field_simp
      ring
    rw [h1, sub_nonneg, div_le_iff₀ hpos] at h
    linarith

end LinearMap.BilinForm
