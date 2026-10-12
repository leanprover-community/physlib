/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import PhyslibAlpha.Mathematics.TauCeti.Analysis.PositiveDefinite.Basic

/-!
# Weighted closure for positive-definite functions

This file adds the weighted finite-mixture and Schur-power API for `TauCeti.IsPositiveDefinite`, the
positive-definite-function predicate on an involutive additive monoid.

## i. Overview

This file adds the weighted finite-mixture and Schur-power API for
`TauCeti.IsPositiveDefinite`, the positive-definite-function predicate on an involutive additive
monoid. The basic file already proves binary sums, nonnegative complex scalar multiples, pointwise
products, and unweighted finite sums/products. Here we package the forms used by examples and
finite approximations: finite nonnegative weighted sums, real-weighted variants, and powers. The
weighted sum API is available in scalar (`•`) notation.

This advances `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part C, the positive-definite
functions API asking for closure under sums and products before the Bochner and BCR representation
milestones. No external formalization is vendored.

## ii. Key results

* `TauCeti.IsPositiveDefinite.real_smul`: nonnegative real scalar multiplication.
* `TauCeti.IsPositiveDefinite.sum_smul`: finite nonnegative weighted sums.
* `TauCeti.IsPositiveDefinite.sum_real_smul`: finite nonnegative real-weighted sums.
* `TauCeti.IsPositiveDefinite.pow`: Schur powers of a positive-definite function.
* `TauCeti.IsPositiveDefinite.sum_smul_apply_zero_of_apply_zero_eq_one`: normalized finite
  mixtures evaluate at the origin as the sum of their weights.

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

variable {M : Type*} [AddMonoid M] [StarAddMonoid M]

/-- Positive-definite functions are closed under multiplication by a nonnegative real scalar. -/
lemma real_smul {r : ℝ} {F : M → ℂ} (hr : 0 ≤ r) (hF : IsPositiveDefinite F) :
    IsPositiveDefinite (fun x => r • F x) := by
  exact hF.const_mul (k := (r : ℂ)) (by exact_mod_cast hr)

/-- Finite nonnegative complex-weighted sums of positive-definite functions are positive
definite. This is the finite-mixture form used when the weights are already complex scalars with
nonnegative real value. -/
lemma sum_smul {ι : Type*} {s : Finset ι} {w : ι → ℂ} {F : ι → M → ℂ}
    (hw : ∀ i ∈ s, 0 ≤ w i) (hF : ∀ i ∈ s, IsPositiveDefinite (F i)) :
    IsPositiveDefinite (fun x => ∑ i ∈ s, w i • F i x) :=
  sum fun i hi => by
    simpa [Algebra.smul_def] using (hF i hi).const_mul (hw i hi)

/-- Finite nonnegative complex-weighted sums, written using multiplication rather than scalar
notation. -/
lemma sum_const_mul {ι : Type*} {s : Finset ι} {w : ι → ℂ} {F : ι → M → ℂ}
    (hw : ∀ i ∈ s, 0 ≤ w i) (hF : ∀ i ∈ s, IsPositiveDefinite (F i)) :
    IsPositiveDefinite (fun x => ∑ i ∈ s, w i * F i x) := by
  simpa [Algebra.smul_def] using sum_smul (M := M) (s := s) (w := w) (F := F) hw hF

/-- Finite nonnegative real-weighted sums of positive-definite functions are positive definite. -/
lemma sum_real_smul {ι : Type*} {s : Finset ι} {w : ι → ℝ} {F : ι → M → ℂ}
    (hw : ∀ i ∈ s, 0 ≤ w i) (hF : ∀ i ∈ s, IsPositiveDefinite (F i)) :
    IsPositiveDefinite (fun x => ∑ i ∈ s, w i • F i x) :=
  sum fun i hi => (hF i hi).real_smul (hw i hi)

/-- Finite nonnegative real-weighted sums, written with the real weight coerced to `ℂ` and
multiplied in the codomain. -/
lemma sum_real_const_mul {ι : Type*} {s : Finset ι} {w : ι → ℝ} {F : ι → M → ℂ}
    (hw : ∀ i ∈ s, 0 ≤ w i) (hF : ∀ i ∈ s, IsPositiveDefinite (F i)) :
    IsPositiveDefinite (fun x => ∑ i ∈ s, (w i : ℂ) * F i x) := by
  simpa [Algebra.smul_def] using sum_real_smul (M := M) (s := s) (w := w) (F := F) hw hF

/-- Schur powers of a positive-definite function are positive definite. -/
lemma pow {F : M → ℂ} (hF : IsPositiveDefinite F) (n : ℕ) :
    IsPositiveDefinite (fun x => F x ^ n) :=
  of_posSemidef (hF.posSemidef.hadamard_pow n)

section Values

variable {N : Type*}

/-- If each summand in a finite complex-weighted sum is normalized at a point, then the sum's
value at that point is the sum of the weights. -/
lemma sum_smul_apply_of_apply_eq_one {ι : Type*} {s : Finset ι} {w : ι → ℂ}
    {F : ι → N → ℂ} {x : N} (hFx : ∀ i ∈ s, F i x = 1) : (∑ i ∈ s, w i • F i x) = ∑ i ∈ s, w i := by
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [hFx i hi]
  simp

/-- A finite complex-weighted sum of functions normalized at a point is normalized at that point
when the weights sum to `1`. -/
lemma sum_smul_apply_eq_one {ι : Type*} {s : Finset ι} {w : ι → ℂ}
    {F : ι → N → ℂ} {x : N} (hFx : ∀ i ∈ s, F i x = 1) (hw_sum : ∑ i ∈ s, w i = 1) :
    (fun y => ∑ i ∈ s, w i • F i y) x = 1 := by
  simpa using (sum_smul_apply_of_apply_eq_one (s := s) (w := w) (F := F) hFx).trans
    hw_sum

/-- If each summand in a finite complex-weighted sum is normalized at a point, then the sum's
multiplication-form value at that point is the sum of the weights. -/
lemma sum_const_mul_apply_of_apply_eq_one {ι : Type*} {s : Finset ι} {w : ι → ℂ}
    {F : ι → N → ℂ} {x : N} (hFx : ∀ i ∈ s, F i x = 1) : (∑ i ∈ s, w i * F i x) = ∑ i ∈ s, w i := by
  simpa [Algebra.smul_def] using
    sum_smul_apply_of_apply_eq_one (s := s) (w := w) (F := F) hFx

/-- A finite complex-weighted sum, in multiplication form, of functions normalized at a point is
normalized at that point when the weights sum to `1`. -/
lemma sum_const_mul_apply_eq_one {ι : Type*} {s : Finset ι} {w : ι → ℂ}
    {F : ι → N → ℂ} {x : N} (hFx : ∀ i ∈ s, F i x = 1) (hw_sum : ∑ i ∈ s, w i = 1) :
    (fun y => ∑ i ∈ s, w i * F i y) x = 1 := by
  simpa [Algebra.smul_def] using
    sum_smul_apply_eq_one (s := s) (w := w) (F := F) hFx hw_sum

/-- If each summand in a finite real-weighted sum is normalized at a point, then the sum's value at
that point is the complex coercion of the sum of the real weights. -/
lemma sum_real_smul_apply_of_apply_eq_one {ι : Type*} {s : Finset ι} {w : ι → ℝ}
    {F : ι → N → ℂ} {x : N} (hFx : ∀ i ∈ s, F i x = 1) :
    (∑ i ∈ s, w i • F i x) = ((∑ i ∈ s, w i : ℝ) : ℂ) := by
  simpa [Algebra.smul_def] using
    sum_smul_apply_of_apply_eq_one (s := s) (w := fun i => (w i : ℂ)) (F := F) hFx

/-- A finite real-weighted sum of functions normalized at a point is normalized at that point when
the weights sum to `1`. -/
lemma sum_real_smul_apply_eq_one {ι : Type*} {s : Finset ι} {w : ι → ℝ}
    {F : ι → N → ℂ} {x : N} (hFx : ∀ i ∈ s, F i x = 1) (hw_sum : ∑ i ∈ s, w i = 1) :
    (fun y => ∑ i ∈ s, w i • F i y) x = 1 := by
  simpa [hw_sum] using
    sum_real_smul_apply_of_apply_eq_one (s := s) (w := w) (F := F) hFx

/-- If each summand in a finite real-weighted sum is normalized at a point, then the sum's
multiplication-form value at that point is the complex coercion of the sum of the real weights. -/
lemma sum_real_const_mul_apply_of_apply_eq_one {ι : Type*} {s : Finset ι}
    {w : ι → ℝ} {F : ι → N → ℂ} {x : N} (hFx : ∀ i ∈ s, F i x = 1) :
    (∑ i ∈ s, (w i : ℂ) * F i x) = ((∑ i ∈ s, w i : ℝ) : ℂ) := by
  simpa [Algebra.smul_def] using
    sum_real_smul_apply_of_apply_eq_one (s := s) (w := w) (F := F) hFx

/-- A finite real-weighted sum, in multiplication form, of functions normalized at a point is
normalized at that point when the weights sum to `1`. -/
lemma sum_real_const_mul_apply_eq_one {ι : Type*} {s : Finset ι} {w : ι → ℝ}
    {F : ι → N → ℂ} {x : N} (hFx : ∀ i ∈ s, F i x = 1) (hw_sum : ∑ i ∈ s, w i = 1) :
    (fun y => ∑ i ∈ s, (w i : ℂ) * F i y) x = 1 := by
  simpa [hw_sum] using
    sum_real_const_mul_apply_of_apply_eq_one (s := s) (w := w) (F := F) hFx

section Origin

variable [Zero N]

/-- If each summand in a finite complex-weighted sum is normalized at the origin, then the sum's
value at the origin is the sum of the weights. -/
lemma sum_smul_apply_zero_of_apply_zero_eq_one {ι : Type*} {s : Finset ι}
    {w : ι → ℂ} {F : ι → N → ℂ} (hF0 : ∀ i ∈ s, F i 0 = 1) :
    (∑ i ∈ s, w i • F i 0) = ∑ i ∈ s, w i :=
  sum_smul_apply_of_apply_eq_one (s := s) (w := w) (F := F) hF0

/-- A finite complex-weighted sum of functions normalized at the origin is normalized when the
weights sum to `1`. -/
lemma sum_smul_apply_zero_eq_one {ι : Type*} {s : Finset ι} {w : ι → ℂ}
    {F : ι → N → ℂ} (hF0 : ∀ i ∈ s, F i 0 = 1) (hw_sum : ∑ i ∈ s, w i = 1) :
    (fun x => ∑ i ∈ s, w i • F i x) 0 = 1 :=
  sum_smul_apply_eq_one (s := s) (w := w) (F := F) hF0 hw_sum

/-- If each summand in a finite complex-weighted sum is normalized at the origin, then the
sum's multiplication-form value at the origin is the sum of the weights. -/
lemma sum_const_mul_apply_zero_of_apply_zero_eq_one {ι : Type*} {s : Finset ι}
    {w : ι → ℂ} {F : ι → N → ℂ} (hF0 : ∀ i ∈ s, F i 0 = 1) :
    (∑ i ∈ s, w i * F i 0) = ∑ i ∈ s, w i :=
  sum_const_mul_apply_of_apply_eq_one (s := s) (w := w) (F := F) hF0

/-- A finite complex-weighted sum, in multiplication form, of functions normalized at the origin is
normalized when the weights sum to `1`. -/
lemma sum_const_mul_apply_zero_eq_one {ι : Type*} {s : Finset ι} {w : ι → ℂ}
    {F : ι → N → ℂ} (hF0 : ∀ i ∈ s, F i 0 = 1) (hw_sum : ∑ i ∈ s, w i = 1) :
    (fun x => ∑ i ∈ s, w i * F i x) 0 = 1 :=
  sum_const_mul_apply_eq_one (s := s) (w := w) (F := F) hF0 hw_sum

/-- If each summand in a finite real-weighted sum is normalized at the origin, then the sum's value
at the origin is the complex coercion of the sum of the real weights. -/
lemma sum_real_smul_apply_zero_of_apply_zero_eq_one {ι : Type*} {s : Finset ι}
    {w : ι → ℝ} {F : ι → N → ℂ} (hF0 : ∀ i ∈ s, F i 0 = 1) :
    (∑ i ∈ s, w i • F i 0) = ((∑ i ∈ s, w i : ℝ) : ℂ) :=
  sum_real_smul_apply_of_apply_eq_one (s := s) (w := w) (F := F) hF0

/-- A finite real-weighted sum of functions normalized at the origin is normalized when the weights
sum to `1`. -/
lemma sum_real_smul_apply_zero_eq_one {ι : Type*} {s : Finset ι} {w : ι → ℝ}
    {F : ι → N → ℂ} (hF0 : ∀ i ∈ s, F i 0 = 1) (hw_sum : ∑ i ∈ s, w i = 1) :
    (fun x => ∑ i ∈ s, w i • F i x) 0 = 1 :=
  sum_real_smul_apply_eq_one (s := s) (w := w) (F := F) hF0 hw_sum

/-- If each summand in a finite real-weighted sum is normalized at the origin, then the sum's
multiplication-form value at the origin is the complex coercion of the sum of the real weights. -/
lemma sum_real_const_mul_apply_zero_of_apply_zero_eq_one {ι : Type*} {s : Finset ι}
    {w : ι → ℝ} {F : ι → N → ℂ} (hF0 : ∀ i ∈ s, F i 0 = 1) :
    (∑ i ∈ s, (w i : ℂ) * F i 0) = ((∑ i ∈ s, w i : ℝ) : ℂ) :=
  sum_real_const_mul_apply_of_apply_eq_one (s := s) (w := w) (F := F) hF0

/-- A finite real-weighted sum, in multiplication form, of functions normalized at the origin is
normalized when the weights sum to `1`. -/
lemma sum_real_const_mul_apply_zero_eq_one {ι : Type*} {s : Finset ι} {w : ι → ℝ}
    {F : ι → N → ℂ} (hF0 : ∀ i ∈ s, F i 0 = 1) (hw_sum : ∑ i ∈ s, w i = 1) :
    (fun x => ∑ i ∈ s, (w i : ℂ) * F i x) 0 = 1 :=
  sum_real_const_mul_apply_eq_one (s := s) (w := w) (F := F) hF0 hw_sum

end Origin

end Values

end IsPositiveDefinite

end TauCeti
