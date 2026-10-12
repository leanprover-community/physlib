/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import PhyslibAlpha.Mathematics.TauCeti.Analysis.PositiveDefinite.Basic

/-!
# Normalizing positive-definite functions

This file records the standard normalization step for positive-definite functions: if `F : M → ℂ` is
positive definite and `F 0 ≠ 0`, then multiplying by the reciprocal of the nonnegative real number
`(F 0).re` gives a positive-definite function whose value at the origin is `1`.

## i. Overview

This file records the standard normalization step for positive-definite functions: if
`F : M → ℂ` is positive definite and `F 0 ≠ 0`, then multiplying by the reciprocal of the
nonnegative real number `(F 0).re` gives a positive-definite function whose value at the origin
is `1`.

This is part of the normalization API requested in Part C of the `OneParameterSemigroups`
roadmap ("Positive-definite functions and Bochner's theorem"). Normalized positive-definite
functions are the convenient form for characteristic functions and for the later Bochner and
GNS/Kolmogorov constructions: after normalization, the general bound `‖F a‖ ≤ (F 0).re` becomes
the familiar `‖F a‖ ≤ 1`.

The file deliberately keeps the hypotheses unbundled. It proves lemmas about the explicit
normalized function rather than introducing a new bundled predicate.

## ii. Key results

* `TauCeti.IsPositiveDefinite.normalize`: multiplying by `((F 0).re)⁻¹` preserves
  positive-definiteness.
* `TauCeti.IsPositiveDefinite.normalize_apply_zero`: the normalized function has value `1` at
  the origin.
* `TauCeti.IsPositiveDefinite.norm_normalize_apply_le_one_of_add_star_eq_zero` and
  `TauCeti.IsPositiveDefinite.norm_normalize_apply_le_one_of_star_eq_neg`: normalized functions
  are bounded by `1` on the usual group-like points.

## iii. Table of contents

- A. Development

## iv. References

* C. Berg, J. P. R. Christensen, P. Ressel, *Harmonic Analysis on Semigroups* (GTM 100, 1984),
  Chapter 3.
-/

public section

/-! ## A. Development -/

open scoped ComplexOrder

namespace TauCeti

namespace IsPositiveDefinite

variable {M : Type*} [AddMonoid M] [StarAddMonoid M] {F : M → ℂ}

/-- The normalizing scalar `((F 0).re)⁻¹`, viewed as a complex number, is nonnegative. -/
private lemma normalizeScalar_nonneg (hF : IsPositiveDefinite F) :
    0 ≤ (((F 0).re)⁻¹ : ℂ) := by
  exact inv_nonneg.mpr ((RCLike.ofReal_nonneg (K := ℂ)).mpr hF.map_zero_re_nonneg)

/-- Multiplying a positive-definite function by the reciprocal of its real value at the origin
preserves positive-definiteness. If `F 0 = 0` this gives the zero scaling; the separate
`normalize_apply_zero` lemma below records the useful nonzero case. -/
lemma normalize (hF : IsPositiveDefinite F) :
    IsPositiveDefinite (fun x => (((F 0).re)⁻¹ : ℂ) * F x) :=
  hF.const_mul hF.normalizeScalar_nonneg

/-- The normalized positive-definite function has value `1` at the origin. -/
@[simp]
lemma normalize_apply_zero (hF : IsPositiveDefinite F) (h0 : F 0 ≠ 0) :
    (((F 0).re)⁻¹ : ℂ) * F 0 = 1 := by
  have hpos := hF.map_zero_re_pos_of_ne_zero h0
  rw [hF.map_zero_eq_ofReal_re]
  norm_cast
  exact inv_mul_cancel₀ hpos.ne'

/-- At points satisfying `a + star a = 0`, the normalized positive-definite function is bounded
by `1`. When `F 0 = 0` the normalizing scalar is `0`, so the bound holds trivially. -/
lemma norm_normalize_apply_le_one_of_add_star_eq_zero (hF : IsPositiveDefinite F)
    (a : M) (ha : a + star a = 0) :
    ‖(((F 0).re)⁻¹ : ℂ) * F a‖ ≤ 1 := by
  rcases hF.map_zero_re_nonneg.lt_or_eq with hpos | hre
  · have hbound := hF.norm_apply_le_map_zero_re_of_add_star_eq_zero a ha
    have hnorm : ‖(((F 0).re)⁻¹ : ℂ)‖ = ((F 0).re)⁻¹ := by
      rw [norm_inv, Complex.norm_of_nonneg hpos.le]
    rw [norm_mul, hnorm]
    have hscale := mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hpos.le)
    rw [inv_mul_cancel₀ hpos.ne'] at hscale
    simpa [mul_comm] using hscale
  · rw [← hre]
    simp

section Group

variable {G : Type*} [AddGroup G] [StarAddMonoid G] {H : G → ℂ}

/-- Under the negation involution, the normalized positive-definite function is bounded by `1` at
every point. -/
lemma norm_normalize_apply_le_one_of_star_eq_neg (hH : IsPositiveDefinite H)
    (a : G) (hstar_a : star a = -a) :
    ‖(((H 0).re)⁻¹ : ℂ) * H a‖ ≤ 1 :=
  hH.norm_normalize_apply_le_one_of_add_star_eq_zero a (by rw [hstar_a, add_neg_cancel])

/-- If the involution is negation everywhere, the normalized positive-definite function is
uniformly bounded by `1`. -/
lemma norm_normalize_apply_le_one_of_forall_star_eq_neg (hH : IsPositiveDefinite H)
    (hstar : ∀ a : G, star a = -a) (a : G) :
    ‖(((H 0).re)⁻¹ : ℂ) * H a‖ ≤ 1 :=
  hH.norm_normalize_apply_le_one_of_star_eq_neg a (hstar a)

end Group

end IsPositiveDefinite

end TauCeti
