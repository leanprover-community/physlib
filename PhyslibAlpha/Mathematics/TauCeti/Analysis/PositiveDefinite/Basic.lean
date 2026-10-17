/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Order
public import Mathlib.Algebra.BigOperators.Fin
public import PhyslibAlpha.Mathematics.TauCeti.Analysis.Matrix.PosSemidef

/-!
# Positive-definite functions on an involutive additive monoid

A complex-valued function `F` on an additive monoid `M` equipped with an involution `star` (an
`AddMonoid` with a `StarAddMonoid` structure) is **positive definite** when, for every finite family
`(cᵢ, aᵢ)` of scalars `cᵢ : ℂ` and points `aᵢ : M`, the Hermitian form `∑_{i,j} cᵢ · conj(cⱼ) · F(aᵢ
+ aⱼ⋆)` is a nonnegative real number.

## i. Overview

A complex-valued function `F` on an additive monoid `M` equipped with an involution `star`
(an `AddMonoid` with a `StarAddMonoid` structure) is **positive definite** when, for every
finite family `(cᵢ, aᵢ)` of scalars `cᵢ : ℂ` and points `aᵢ : M`, the Hermitian form
`∑_{i,j} cᵢ · conj(cⱼ) · F(aᵢ + aⱼ⋆)` is a nonnegative real number. The involution `aⱼ⋆` inside
the argument is what makes this the right notion on an involutive semigroup (Berg–Christensen–
Ressel): on a finite-dimensional real inner-product space with `a⋆ = -a` it specialises to the
classical translation-invariant positive-definiteness `∑ cᵢ conj(cⱼ) F(aᵢ - aⱼ) ≥ 0`, and on the
product monoid `ℝ≥0 × V` it produces the BCR involution `(t, a)⋆ = (t, -a)`.

This file introduces the predicate `TauCeti.IsPositiveDefinite` at this general level and develops
its basic algebraic API: the value at `0` is real and nonnegative, the function is conjugate
symmetric in the involution, it satisfies the Cauchy–Schwarz inequality coming from the `2 × 2`
sub-form, and the class is closed under sums and nonnegative complex scalar multiples, with the
Schur pointwise product closure and nonnegative constants as examples.

This is the `Objects` and first `API to develop` slice of Part C of the `OneParameterSemigroups`
roadmap in TauCetiRoadmap: "positive-definite functions and Bochner's theorem". Mathlib has
related APIs for positive-semidefinite matrices, bilinear and linear maps, and RKHS kernels, but
not for positive-definite functions on an involutive monoid, so the predicate and its API are built
here. The continuity theory and Bochner's representation theorem are later milestones.

## ii. Key results

* `TauCeti.IsPositiveDefinite`: the positive-definiteness predicate for `F : M → ℂ`.
* `TauCeti.IsPositiveDefinite.sum_nonneg`: nonnegativity for arbitrary finite families.
* `TauCeti.IsPositiveDefinite.quadForm_two_nonneg`: nonnegativity of the `2 × 2` sub-form.
* `TauCeti.IsPositiveDefinite.map_zero_nonneg`: `0 ≤ F 0`.
* `TauCeti.IsPositiveDefinite.map_zero_im`: `(F 0).im = 0`.
* `TauCeti.IsPositiveDefinite.map_zero_re_nonneg`: `0 ≤ (F 0).re`.
* `TauCeti.IsPositiveDefinite.map_zero_eq_ofReal_re`: `F 0 = ((F 0).re : ℂ)`.
* `TauCeti.IsPositiveDefinite.map_zero_re_pos_of_ne_zero`: if `F 0 ≠ 0`, then
  `0 < (F 0).re`.
* `TauCeti.IsPositiveDefinite.conj_symm`: `conj (F (b + a⋆)) = F (a + b⋆)`.
* `TauCeti.IsPositiveDefinite.normSq_le`: the Cauchy–Schwarz inequality
  `‖F (a + b⋆)‖² ≤ (F (a + a⋆)).re * (F (b + b⋆)).re`.
* `TauCeti.IsPositiveDefinite.norm_apply_le_map_zero_re_of_add_star_eq_zero`: `‖F a‖ ≤ (F 0).re`
  when `a + star a = 0`, with the additive-group corollary
  `TauCeti.IsPositiveDefinite.norm_apply_le_map_zero_re_of_star_eq_neg` for `star a = -a`.
* `TauCeti.IsPositiveDefinite.apply_eq_zero_of_map_zero_re_eq_zero`: `(F 0).re = 0` forces
  `F` to vanish identically.
* `TauCeti.IsPositiveDefinite.posSemidef`: a positive-definite function gives the
  positive-definite kernel `fun a b => F (a + star b)`.
* `TauCeti.IsPositiveDefinite.of_posSemidef`: conversely, if the kernel
  `fun a b => F (a + star b)` is positive definite then `F` is positive definite.
* `TauCeti.IsPositiveDefinite.add`, `TauCeti.IsPositiveDefinite.sum`,
  `TauCeti.IsPositiveDefinite.const_mul`, `TauCeti.IsPositiveDefinite.mul`,
  `TauCeti.IsPositiveDefinite.prod`, `TauCeti.isPositiveDefinite_const`: closure properties and
  examples.

## iii. Table of contents

- A. Development

## iv. References

* C. Berg, J. P. R. Christensen, P. Ressel, *Harmonic Analysis on Semigroups* (GTM 100, 1984),
  Chapter 3.
-/

public section

/-! ## A. Development -/

open ComplexConjugate
open scoped ComplexOrder

namespace TauCeti

variable {M : Type*} [AddMonoid M] [StarAddMonoid M] {F G : M → ℂ}

/-- A function `F : M → ℂ` on an involutive additive monoid is **positive definite** when, for
every finite family of scalars `c : Fin n → ℂ` and points `v : Fin n → M`, the Hermitian form
`∑_{i,j} c i · conj (c j) · F (v i + star (v j))` is a nonnegative real number (using the order on
`ℂ` for which `0 ≤ z` means `z` is real and nonnegative). -/
@[expose] def IsPositiveDefinite (F : M → ℂ) : Prop :=
  ∀ (n : ℕ) (c : Fin n → ℂ) (v : Fin n → M),
    0 ≤ ∑ i, ∑ j, c i * conj (c j) * F (v i + star (v j))

namespace IsPositiveDefinite

/-- Positive-definiteness holds for an arbitrary finite index type, not just `Fin n`: for every
finite family of scalars `c : ι → ℂ` and points `v : ι → M`, the Hermitian form
`∑_{i,j} c i · conj (c j) · F (v i + star (v j))` is a nonnegative real number. -/
lemma sum_nonneg (hF : IsPositiveDefinite F) {ι : Type*} [Fintype ι] (c : ι → ℂ) (v : ι → M) :
    0 ≤ ∑ i, ∑ j, c i * conj (c j) * F (v i + star (v j)) := by
  classical
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have h := hF (Fintype.card ι) (fun i => c (e i)) (fun i => v (e i))
  refine le_of_le_of_eq h ?_
  exact Fintype.sum_equiv e _ _ fun i =>
    Fintype.sum_equiv e _ _ fun j => rfl

/-- The `2 × 2` Hermitian sub-form of a positive-definite function at the points `a, b` with
coefficients `c₀, c₁` is nonnegative. -/
lemma quadForm_two_nonneg (hF : IsPositiveDefinite F) (a b : M) (c₀ c₁ : ℂ) :
    0 ≤ c₀ * conj c₀ * F (a + star a) + c₀ * conj c₁ * F (a + star b)
      + c₁ * conj c₀ * F (b + star a) + c₁ * conj c₁ * F (b + star b) := by
  have h := hF 2 ![c₀, c₁] ![a, b]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  exact le_of_le_of_eq h (by ring)

/-- A positive-definite function takes a real, nonnegative value at every "norm point"
`a + star a`. -/
lemma add_star_self_nonneg (hF : IsPositiveDefinite F) (a : M) : 0 ≤ F (a + star a) := by
  have h := hF 1 ![1] ![a]
  simpa [Fin.sum_univ_one] using h

/-- The value of a positive-definite function at a "norm point" `a + star a` has zero imaginary
part. -/
lemma add_star_self_im (hF : IsPositiveDefinite F) (a : M) : (F (a + star a)).im = 0 :=
  ((Complex.nonneg_iff.mp (hF.add_star_self_nonneg a)).2).symm

/-- The value of a positive-definite function at a "norm point" `a + star a` has nonnegative real
part. -/
lemma add_star_self_re_nonneg (hF : IsPositiveDefinite F) (a : M) : 0 ≤ (F (a + star a)).re :=
  (Complex.nonneg_iff.mp (hF.add_star_self_nonneg a)).1

/-- The value of a positive-definite function at `0` is real and nonnegative. -/
lemma map_zero_nonneg (hF : IsPositiveDefinite F) : 0 ≤ F 0 := by
  simpa [star_zero] using hF.add_star_self_nonneg 0

/-- The value of a positive-definite function at `0` has zero imaginary part. -/
@[simp]
lemma map_zero_im (hF : IsPositiveDefinite F) : (F 0).im = 0 :=
  ((Complex.nonneg_iff.mp hF.map_zero_nonneg).2).symm

/-- The real part of the value of a positive-definite function at `0` is nonnegative. -/
lemma map_zero_re_nonneg (hF : IsPositiveDefinite F) : 0 ≤ (F 0).re :=
  (Complex.nonneg_iff.mp hF.map_zero_nonneg).1

/-- The value at the origin of a positive-definite function is equal to the real number
`(F 0).re`, viewed as a complex number. -/
lemma map_zero_eq_ofReal_re (hF : IsPositiveDefinite F) : F 0 = ((F 0).re : ℂ) := by
  apply Complex.ext
  · simp
  · simpa using hF.map_zero_im

/-- If a positive-definite function is nonzero at the origin, then the real part of that value is
strictly positive. -/
lemma map_zero_re_pos_of_ne_zero (hF : IsPositiveDefinite F) (h0 : F 0 ≠ 0) :
    0 < (F 0).re := by
  refine lt_of_le_of_ne hF.map_zero_re_nonneg ?_
  intro hre
  apply h0
  apply Complex.ext
  · exact hre.symm
  · simpa using hF.map_zero_im

/-- A positive-definite function is conjugate symmetric in the involution:
`conj (F (b + star a)) = F (a + star b)`. -/
@[simp]
lemma conj_symm (hF : IsPositiveDefinite F) (a b : M) :
    conj (F (b + star a)) = F (a + star b) := by
  -- The diagonal entries `F (a + star a)`, `F (b + star b)` are real.
  have hp := hF.add_star_self_im a
  have hq := hF.add_star_self_im b
  -- Coefficients `(1, 1)` force the imaginary parts of the off-diagonal entries to be opposite.
  have him : (F (b + star a)).im + (F (a + star b)).im = 0 := by
    have h := (Complex.nonneg_iff.mp (hF.quadForm_two_nonneg a b 1 1)).2
    simp [Complex.add_im, hp, hq] at h
    linarith
  -- Coefficients `(1, I)` force the real parts of the off-diagonal entries to be equal.
  have hre : (F (b + star a)).re = (F (a + star b)).re := by
    have h := (Complex.nonneg_iff.mp (hF.quadForm_two_nonneg a b 1 Complex.I)).2
    simp [Complex.add_im, Complex.mul_im, hp, hq] at h
    linarith
  apply Complex.ext
  · rw [Complex.conj_re]; exact hre
  · rw [Complex.conj_im]; linarith

/-- A positive-definite function `F` induces the positive-definite kernel `K(a, b) = F(a + b⋆)`.
This is the forward half of the function ↔ kernel correspondence. -/
lemma posSemidef (hF : IsPositiveDefinite F) :
    Matrix.PosSemidef (fun a b => F (a + star b)) :=
  posSemidef_iff_finite_sum.mpr
    ⟨fun a b => by simpa only [RCLike.star_def] using hF.conj_symm b a,
      fun {_ι : Type} _ v x => by
      have h := hF.sum_nonneg (fun i => conj (x i)) v
      refine le_of_le_of_eq h ?_
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [RCLike.star_def, Complex.conj_conj]
      ring⟩

/-- If the kernel `K(a, b) = F(a + b⋆)` is positive definite, then so is the function `F`. This is
the reverse half of the function ↔ kernel correspondence. -/
lemma of_posSemidef
    (hK : Matrix.PosSemidef (fun a b => F (a + star b))) : IsPositiveDefinite F := by
  obtain ⟨_, hpos⟩ := posSemidef_iff_finite_sum.mp hK
  intro n c v
  have h := hpos v (fun i => conj (c i))
  refine le_of_le_of_eq h ?_
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [RCLike.star_def, Complex.conj_conj]
  ring

/-- The Cauchy–Schwarz inequality for a positive-definite function: the squared norm of an
off-diagonal value is bounded by the product of the two diagonal values. -/
lemma normSq_le (hF : IsPositiveDefinite F) (a b : M) :
    Complex.normSq (F (a + star b))
      ≤ (F (a + star a)).re * (F (b + star b)).re :=
  hF.posSemidef.normSq_le a b

/-- If `a + star a = 0`, then a positive-definite function is bounded at `a` by its value at
zero. -/
lemma norm_apply_le_map_zero_re_of_add_star_eq_zero (hF : IsPositiveDefinite F)
    (a : M) (ha : a + star a = 0) : ‖F a‖ ≤ (F 0).re := by
  refine le_of_sq_le_sq ?_ hF.map_zero_re_nonneg
  simpa [Complex.normSq_eq_norm_sq, pow_two, ha, star_zero] using hF.normSq_le a 0

-- Not a `simp` lemma: the conclusion is `F a = 0` with `F` a variable, so the left-hand side has
-- a variable head symbol. Lean rejects the tag outright ("the theorem will be tried on every simp
-- step"), and `warningAsError` makes that a build failure. The sibling bound
-- `norm_apply_le_map_zero_re_of_add_star_eq_zero` is untagged for the same reason.
/-- **A positive-definite function with `(F 0).re = 0` vanishes identically.**

No hypothesis on the point is required, and none on the ambient structure beyond an
involutive additive monoid (`AddMonoid` and `StarAddMonoid`). -/
lemma apply_eq_zero_of_map_zero_re_eq_zero (hF : IsPositiveDefinite F)
    (h0 : (F 0).re = 0) (a : M) : F a = 0 := by
  have hzero : F (0 + star 0) = 0 := by simpa [h0] using hF.map_zero_eq_ofReal_re
  simpa using hF.posSemidef.eq_zero_of_apply_self_eq_zero_right
    (a := a) (b := 0) hzero

section Group

variable {N : Type*} [AddGroup N] [StarAddMonoid N] {H : N → ℂ}

/-- If the involution negates the point `a`, then a positive-definite function is bounded at `a`
by its value at zero. In particular this applies on an additive group whose involution is
negation. -/
lemma norm_apply_le_map_zero_re_of_star_eq_neg (hH : IsPositiveDefinite H)
    (a : N) (hstar_a : star a = -a) : ‖H a‖ ≤ (H 0).re :=
  hH.norm_apply_le_map_zero_re_of_add_star_eq_zero a (by rw [hstar_a, add_neg_cancel])

end Group

/-- Positive-definite functions are closed under addition. -/
lemma add (hF : IsPositiveDefinite F) (hG : IsPositiveDefinite G) :
    IsPositiveDefinite (fun x => F x + G x) :=
  of_posSemidef <|
    hF.posSemidef.add hG.posSemidef

/-- Positive-definite functions are closed under multiplication by a nonnegative complex scalar. -/
lemma const_mul {k : ℂ} (hk : 0 ≤ k) (hF : IsPositiveDefinite F) :
    IsPositiveDefinite (fun x => k * F x) :=
  of_posSemidef <|
    hF.posSemidef.smul hk

/-- Positive-definite functions are closed under pointwise multiplication (Schur product). -/
lemma mul (hF : IsPositiveDefinite F) (hG : IsPositiveDefinite G) :
    IsPositiveDefinite (fun x => F x * G x) :=
  of_posSemidef <|
    hF.posSemidef.hadamard hG.posSemidef

end IsPositiveDefinite

/-- A nonnegative real constant is a positive-definite function. -/
lemma isPositiveDefinite_const {k : ℂ} (hk : 0 ≤ k) :
    IsPositiveDefinite (fun _ : M => k) :=
  IsPositiveDefinite.of_posSemidef <|
    posSemidef_const_of_nonneg hk

/-- The zero function is positive definite. -/
lemma isPositiveDefinite_zero : IsPositiveDefinite (fun _ : M => (0 : ℂ)) :=
  isPositiveDefinite_const le_rfl

namespace IsPositiveDefinite

/-- Positive-definite functions are closed under finite sums. -/
lemma sum {ι : Type*} {s : Finset ι} {F : ι → M → ℂ} (hF : ∀ i ∈ s, IsPositiveDefinite (F i)) :
    IsPositiveDefinite (fun x => ∑ i ∈ s, F i x) := by
  apply of_posSemidef
  have heq : (∑ i ∈ s, fun a b : M => F i (a + star b)) =
      (fun a b : M => ∑ i ∈ s, F i (a + star b)) := by ext; simp
  exact heq ▸ Matrix.posSemidef_sum s (fun i hi => (hF i hi).posSemidef)

/-- Positive-definite functions are closed under finite products (Schur product). -/
lemma prod {ι : Type*} {s : Finset ι} {F : ι → M → ℂ} (hF : ∀ i ∈ s, IsPositiveDefinite (F i)) :
    IsPositiveDefinite (fun x => ∏ i ∈ s, F i x) :=
  of_posSemidef <|
    posSemidef_schur_finset_prod fun i hi => (hF i hi).posSemidef

end IsPositiveDefinite

end TauCeti
