/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import PhyslibAlpha.Mathematics.TauCeti.Analysis.PositiveDefinite.Continuity
public import PhyslibAlpha.Mathematics.TauCeti.Analysis.PositiveDefinite.Function.Closure
public import PhyslibAlpha.Mathematics.TauCeti.Analysis.PositiveDefinite.Function.Kernel
public import PhyslibAlpha.Mathematics.TauCeti.Analysis.PositiveDefinite.Limits
public import PhyslibAlpha.Mathematics.TauCeti.Analysis.PositiveDefinite.Normalize

/-!
# Positive-definite functions on an additive commutative group

On an additive commutative group `G` the classical positive-definiteness condition for `F : G → ℂ`
reads `∑_{i,j} cᵢ · conj(cⱼ) · F(aᵢ - aⱼ) ≥ 0`: the involution is negation, so the kernel is the
translation-invariant `K(a, b) = F(a - b)`.

## i. Overview

On an additive commutative group `G` the classical positive-definiteness condition for
`F : G → ℂ` reads `∑_{i,j} cᵢ · conj(cⱼ) · F(aᵢ - aⱼ) ≥ 0`: the involution is negation, so the
kernel is the translation-invariant `K(a, b) = F(a - b)`. Mathlib's `star` on a real vector space
is the identity, not negation, so the generic involutive predicate
`TauCeti.IsPositiveDefinite` does *not* express this condition for the canonical instances on
`ℝ` or on a Euclidean space. This file supplies the subtraction-form predicate
`TauCeti.IsPositiveDefiniteSub` that does, and connects it to the generic theory.

The connection runs through the type synonym `TauCeti.WithNegStar G`, a copy of `G` carrying the
negation involution `star a = -a` as a genuine `StarAddMonoid` instance. Installing that
involution on `G` itself would clash with Mathlib's star conventions, so it is installed on the
synonym instead, and `TauCeti.isPositiveDefiniteSub_iff_isPositiveDefinite` transports statements
across. The synonym is public: a generic lemma with no transfer lemma here can still be applied to
`fun a : WithNegStar G => F (WithNegStar.ofNegStar a)`.

This advances `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part C, Objects, which asks for
`IsPositiveDefinite` to be defined generically and then *instantiated* on a finite-dimensional real
inner-product space with the involution `a⋆ = -a`, and the `API to develop` items (closure
properties, the value bounds at the origin, continuity at `0` implying uniform continuity, the
PD-function ↔ PD-kernel equivalence `F(a - b)`, and normalization) at that instantiation. It is
the predicate in which Bochner's theorem is stated, in
`TauCeti/Analysis/Bochner/BochnerTheorem.lean`.

## ii. Key results

* `TauCeti.WithNegStar`: the type synonym carrying the negation involution.
* `TauCeti.IsPositiveDefiniteSub`: the subtraction-form positive-definiteness predicate.
* `TauCeti.isPositiveDefiniteSub_iff_forall_sum_nonneg`: the defining finite-family condition.
* `TauCeti.isPositiveDefiniteSub_iff_isPositiveDefinite`: the transfer to the generic predicate.
* `TauCeti.isPositiveDefiniteSub_iff_posSemidef`: the PD-function ↔ PD-kernel equivalence.
* `TauCeti.isPositiveDefinite_iff_isPositiveDefiniteSub`: agreement with the generic predicate on
  a group whose own involution is negation.
* `TauCeti.IsPositiveDefiniteSub.map_zero_nonneg`, `map_zero_re_nonneg`, `map_zero_eq_ofReal_re`,
  `map_neg`, `conj_symm`, `normSq_le`, `norm_apply_le_map_zero_re`: values at and around the
  origin.
* `TauCeti.IsPositiveDefiniteSub.add`, `const_mul`, `real_smul`, `mul`, `sum`, `prod`,
  `TauCeti.isPositiveDefiniteSub_const`: closure properties.
* `TauCeti.IsPositiveDefiniteSub.comp_addMonoidHom`, `comp_smul`, `comp_neg`: pullbacks.
* `TauCeti.IsPositiveDefiniteSub.of_tendsto`: pointwise limits.
* `TauCeti.IsPositiveDefiniteSub.normalize`: normalization to value `1` at the origin.
* `TauCeti.IsPositiveDefiniteSub.uniformContinuous_of_continuousAt_zero`: continuity at `0`
  implies uniform continuity.

## iii. Table of contents

- A. Development
  - A.1. The negation involution
  - A.2. The subtraction-form predicate
  - A.3. Values at and around the origin
  - A.4. Closure properties
  - A.5. Pullbacks
  - A.6. Limits
  - A.7. Normalization
  - A.8. Continuity

## iv. References

* C. Berg, J. P. R. Christensen, P. Ressel, *Harmonic Analysis on Semigroups* (GTM 100, 1984),
  Chapter 3.
* W. Rudin, *Fourier Analysis on Groups* (1962), §1.4.
-/

public section

/-! ## A. Development -/

open ComplexConjugate Filter
open scoped ComplexOrder Topology

namespace TauCeti

/-! ### A.1. The negation involution -/

/-- `WithNegStar G` is a type synonym for an additive commutative group `G`, carrying the negation
involution `star a = -a`.

Mathlib pins no negation `StarAddMonoid` instance on an additive group — on a real vector space
`star` is the identity — so the involution used by classical positive definiteness is installed on
this synonym rather than on `G` itself. -/
@[expose] def WithNegStar (G : Type*) : Type _ := G

namespace WithNegStar

section AddCommGroup

variable {G : Type*} [AddCommGroup G]

instance : AddCommGroup (WithNegStar G) := inferInstanceAs (AddCommGroup G)

instance : Star (WithNegStar G) := ⟨fun a => -a⟩

@[simp]
lemma star_eq_neg (a : WithNegStar G) : star a = -a := rfl

instance : StarAddMonoid (WithNegStar G) where
  star_involutive a := neg_neg a
  star_add a b := neg_add a b

/-- The identity additive equivalence from `G` to its negation-involution copy. -/
def toNegStar : G ≃+ WithNegStar G := AddEquiv.refl G

/-- The identity additive equivalence from the negation-involution copy of `G` back to `G`. -/
def ofNegStar : WithNegStar G ≃+ G := toNegStar.symm

@[simp]
lemma ofNegStar_toNegStar (a : G) : ofNegStar (toNegStar a) = a :=
  toNegStar.symm_apply_apply a

@[simp]
lemma toNegStar_ofNegStar (a : WithNegStar G) : toNegStar (ofNegStar a) = a :=
  toNegStar.apply_symm_apply a

end AddCommGroup

section Seminormed

variable {G : Type*} [SeminormedAddCommGroup G]

instance : SeminormedAddCommGroup (WithNegStar G) :=
  inferInstanceAs (SeminormedAddCommGroup G)

end Seminormed

end WithNegStar

/-! ### A.2. The subtraction-form predicate -/

variable {G : Type*} [AddCommGroup G] {F H : G → ℂ}

/-- A function `F : G → ℂ` on an additive commutative group is **positive definite** when, for
every finite family of scalars `c : Fin n → ℂ` and points `v : Fin n → G`, the Hermitian form
`∑_{i,j} c i · conj (c j) * F (v i - v j)` is a nonnegative real number (using the order on `ℂ`
for which `0 ≤ z` means `z` is real and nonnegative).

This is the classical translation-invariant condition, the one Bochner's theorem is stated in. It
is `TauCeti.IsPositiveDefinite` for the negation involution; see
`TauCeti.isPositiveDefiniteSub_iff_isPositiveDefinite`. -/
def IsPositiveDefiniteSub (F : G → ℂ) : Prop :=
  ∀ (n : ℕ) (c : Fin n → ℂ) (v : Fin n → G),
    0 ≤ ∑ i, ∑ j, c i * conj (c j) * F (v i - v j)

/-- The defining finite-family characterization, for building a positive-definite function
directly from the quadratic-form condition. -/
lemma isPositiveDefiniteSub_iff_forall_sum_nonneg :
    IsPositiveDefiniteSub F ↔ ∀ (n : ℕ) (c : Fin n → ℂ) (v : Fin n → G),
      0 ≤ ∑ i, ∑ j, c i * conj (c j) * F (v i - v j) :=
  Iff.rfl

/-- Subtraction-form positive definiteness is the generic involutive predicate for the negation
involution, read on the type synonym `TauCeti.WithNegStar`. -/
lemma isPositiveDefiniteSub_iff_isPositiveDefinite :
    IsPositiveDefiniteSub F ↔
      IsPositiveDefinite fun a : WithNegStar G => F (WithNegStar.ofNegStar a) := by
  constructor
  · intro hF n c v
    simpa [sub_eq_add_neg] using hF n c fun i => WithNegStar.ofNegStar (v i)
  · intro hF n c v
    simpa [sub_eq_add_neg] using hF n c fun i => WithNegStar.toNegStar (v i)

namespace IsPositiveDefiniteSub

/-- The generic involutive predicate attached to a subtraction-form positive-definite function.
This is the workhorse for transporting the generic API. -/
lemma isPositiveDefinite (hF : IsPositiveDefiniteSub F) :
    IsPositiveDefinite fun a : WithNegStar G => F (WithNegStar.ofNegStar a) :=
  isPositiveDefiniteSub_iff_isPositiveDefinite.mp hF

/-- Positive-definiteness holds for an arbitrary finite index type, not just `Fin n`. -/
lemma sum_nonneg (hF : IsPositiveDefiniteSub F) {ι : Type*} [Fintype ι] (c : ι → ℂ) (v : ι → G) :
    0 ≤ ∑ i, ∑ j, c i * conj (c j) * F (v i - v j) := by
  simpa [sub_eq_add_neg] using
    hF.isPositiveDefinite.sum_nonneg c fun i => WithNegStar.toNegStar (v i)

/-- A subtraction-form positive-definite function gives the translation-invariant
positive-definite kernel `K(a, b) = F (a - b)`. -/
lemma posSemidef (hF : IsPositiveDefiniteSub F) :
    Matrix.PosSemidef fun a b : G => F (a - b) := by
  have h := hF.isPositiveDefinite.posSemidef.submatrix fun a : G => WithNegStar.toNegStar a
  have heq : Matrix.submatrix
      (Matrix.of fun a b : WithNegStar G =>
        F (WithNegStar.ofNegStar (a + star b)))
      (fun a : G => WithNegStar.toNegStar a) (fun a : G => WithNegStar.toNegStar a) =
      fun a b : G => F (a - b) := by
    ext a b
    simp [sub_eq_add_neg]
  exact heq ▸ h

/-- A function whose translation-invariant kernel `K(a, b) = F (a - b)` is positive definite is
positive definite. -/
lemma of_posSemidef (hK : Matrix.PosSemidef fun a b : G => F (a - b)) :
    IsPositiveDefiniteSub F := by
  refine isPositiveDefiniteSub_iff_isPositiveDefinite.mpr
    (IsPositiveDefinite.of_posSemidef ?_)
  have h := hK.submatrix fun a : WithNegStar G => WithNegStar.ofNegStar a
  have heq : Matrix.submatrix (Matrix.of fun a b : G => F (a - b))
      (fun a : WithNegStar G => WithNegStar.ofNegStar a)
      (fun a : WithNegStar G => WithNegStar.ofNegStar a) =
      fun a b : WithNegStar G => F (WithNegStar.ofNegStar (a + star b)) := by
    ext a b
    simp [sub_eq_add_neg]
  exact heq ▸ h

end IsPositiveDefiniteSub

/-- The PD-function ↔ PD-kernel equivalence in its classical translation-invariant form: `F` is
positive definite if and only if the kernel `K(a, b) = F (a - b)` is positive definite. -/
lemma isPositiveDefiniteSub_iff_posSemidef :
    IsPositiveDefiniteSub F ↔ Matrix.PosSemidef fun a b : G => F (a - b) :=
  ⟨IsPositiveDefiniteSub.posSemidef, IsPositiveDefiniteSub.of_posSemidef⟩

/-- On a group whose own involution is negation, the generic involutive predicate and the
subtraction-form predicate agree. -/
lemma isPositiveDefinite_iff_isPositiveDefiniteSub [StarAddMonoid G]
    (hstar : ∀ a : G, star a = -a) : IsPositiveDefinite F ↔ IsPositiveDefiniteSub F :=
  (isPositiveDefinite_iff_posSemidef_sub hstar).trans isPositiveDefiniteSub_iff_posSemidef.symm

/-! ### A.3. Values at and around the origin -/

namespace IsPositiveDefiniteSub

/-- The value of a positive-definite function at `0` is real and nonnegative. -/
lemma map_zero_nonneg (hF : IsPositiveDefiniteSub F) : 0 ≤ F 0 := by
  simpa using hF.isPositiveDefinite.map_zero_nonneg

/-- The value of a positive-definite function at `0` has zero imaginary part. -/
@[simp]
lemma map_zero_im (hF : IsPositiveDefiniteSub F) : (F 0).im = 0 :=
  ((Complex.nonneg_iff.mp hF.map_zero_nonneg).2).symm

/-- The real part of the value of a positive-definite function at `0` is nonnegative. -/
lemma map_zero_re_nonneg (hF : IsPositiveDefiniteSub F) : 0 ≤ (F 0).re :=
  (Complex.nonneg_iff.mp hF.map_zero_nonneg).1

/-- The value at the origin of a positive-definite function is the real number `(F 0).re`, viewed
as a complex number. -/
lemma map_zero_eq_ofReal_re (hF : IsPositiveDefiniteSub F) : F 0 = ((F 0).re : ℂ) := by
  simpa using hF.isPositiveDefinite.map_zero_eq_ofReal_re

/-- If a positive-definite function is nonzero at the origin, then the real part of that value is
strictly positive. -/
lemma map_zero_re_pos_of_ne_zero (hF : IsPositiveDefiniteSub F) (h0 : F 0 ≠ 0) :
    0 < (F 0).re := by
  refine hF.isPositiveDefinite.map_zero_re_pos_of_ne_zero ?_
  simpa using h0

/-- A positive-definite function is conjugate symmetric: `conj (F (b - a)) = F (a - b)`. -/
@[simp]
lemma conj_symm (hF : IsPositiveDefiniteSub F) (a b : G) : conj (F (b - a)) = F (a - b) := by
  simpa [sub_eq_add_neg] using
    hF.isPositiveDefinite.conj_symm (WithNegStar.toNegStar a) (WithNegStar.toNegStar b)

/-- A positive-definite function satisfies `F (-a) = conj (F a)`. -/
lemma map_neg (hF : IsPositiveDefiniteSub F) (a : G) : F (-a) = conj (F a) := by
  simpa using (hF.conj_symm 0 a).symm

/-- The Cauchy–Schwarz inequality for a positive-definite function: the squared norm of any value
is bounded by the square of the value at the origin. -/
lemma normSq_le (hF : IsPositiveDefiniteSub F) (a b : G) :
    Complex.normSq (F (a - b)) ≤ (F 0).re * (F 0).re := by
  simpa [sub_eq_add_neg] using
    hF.isPositiveDefinite.normSq_le (WithNegStar.toNegStar a) (WithNegStar.toNegStar b)

/-- A positive-definite function is bounded by its value at the origin. -/
lemma norm_apply_le_map_zero_re (hF : IsPositiveDefiniteSub F) (a : G) : ‖F a‖ ≤ (F 0).re := by
  simpa using hF.isPositiveDefinite.norm_apply_le_map_zero_re_of_star_eq_neg
    (WithNegStar.toNegStar a) rfl

-- Not a `simp` lemma: the conclusion `F a = 0` has a variable head symbol, which Lean rejects.
/-- **A positive-definite function with `(F 0).re = 0` vanishes identically.** -/
lemma apply_eq_zero_of_map_zero_re_eq_zero (hF : IsPositiveDefiniteSub F) (h0 : (F 0).re = 0)
    (a : G) : F a = 0 := by
  simpa using hF.isPositiveDefinite.apply_eq_zero_of_map_zero_re_eq_zero (by simpa using h0)
    (WithNegStar.toNegStar a)

/-! ### A.4. Closure properties -/

/-- Positive-definite functions are closed under addition. -/
lemma add (hF : IsPositiveDefiniteSub F) (hH : IsPositiveDefiniteSub H) :
    IsPositiveDefiniteSub fun x => F x + H x :=
  isPositiveDefiniteSub_iff_isPositiveDefinite.mpr
    (hF.isPositiveDefinite.add hH.isPositiveDefinite)

/-- Positive-definite functions are closed under multiplication by a nonnegative complex
scalar. -/
lemma const_mul {k : ℂ} (hk : 0 ≤ k) (hF : IsPositiveDefiniteSub F) :
    IsPositiveDefiniteSub fun x => k * F x :=
  isPositiveDefiniteSub_iff_isPositiveDefinite.mpr (hF.isPositiveDefinite.const_mul hk)

/-- Positive-definite functions are closed under multiplication by a nonnegative real scalar. -/
lemma real_smul {r : ℝ} (hr : 0 ≤ r) (hF : IsPositiveDefiniteSub F) :
    IsPositiveDefiniteSub fun x => r • F x :=
  isPositiveDefiniteSub_iff_isPositiveDefinite.mpr (hF.isPositiveDefinite.real_smul hr)

/-- Positive-definite functions are closed under pointwise multiplication (Schur product). -/
lemma mul (hF : IsPositiveDefiniteSub F) (hH : IsPositiveDefiniteSub H) :
    IsPositiveDefiniteSub fun x => F x * H x :=
  isPositiveDefiniteSub_iff_isPositiveDefinite.mpr
    (hF.isPositiveDefinite.mul hH.isPositiveDefinite)

/-- Positive-definite functions are closed under finite sums. -/
lemma sum {ι : Type*} {s : Finset ι} {F : ι → G → ℂ}
    (hF : ∀ i ∈ s, IsPositiveDefiniteSub (F i)) :
    IsPositiveDefiniteSub fun x => ∑ i ∈ s, F i x :=
  isPositiveDefiniteSub_iff_isPositiveDefinite.mpr
    (IsPositiveDefinite.sum fun i hi => (hF i hi).isPositiveDefinite)

/-- Positive-definite functions are closed under finite products (Schur products). -/
lemma prod {ι : Type*} {s : Finset ι} {F : ι → G → ℂ}
    (hF : ∀ i ∈ s, IsPositiveDefiniteSub (F i)) :
    IsPositiveDefiniteSub fun x => ∏ i ∈ s, F i x :=
  isPositiveDefiniteSub_iff_isPositiveDefinite.mpr
    (IsPositiveDefinite.prod fun i hi => (hF i hi).isPositiveDefinite)

/-! ### A.5. Pullbacks -/

/-- Positive definiteness is preserved by precomposition with an additive homomorphism; no
compatibility with an involution is needed, since an additive homomorphism automatically
commutes with negation. -/
lemma comp_addMonoidHom {N : Type*} [AddCommGroup N] (hF : IsPositiveDefiniteSub F)
    (φ : N →+ G) : IsPositiveDefiniteSub fun x => F (φ x) := by
  intro n c v
  simpa [← map_sub] using hF n c fun i => φ (v i)

/-- Positive definiteness is preserved by rescaling the argument. -/
lemma comp_smul {R : Type*} [DistribSMul R G] (hF : IsPositiveDefiniteSub F) (r : R) :
    IsPositiveDefiniteSub fun x => F (r • x) := by
  intro n c v
  simpa [← smul_sub] using hF n c fun i => r • v i

/-- Positive definiteness is preserved by negating the argument. -/
lemma comp_neg (hF : IsPositiveDefiniteSub F) : IsPositiveDefiniteSub fun x => F (-x) := by
  intro n c v
  simpa [neg_sub, sub_eq_neg_add, add_comm] using hF n c fun i => -v i

/-! ### A.6. Limits -/

/-- Positive definiteness is preserved under pointwise limits along a nontrivial filter. -/
lemma of_tendsto {ι : Type*} {l : Filter ι} [NeBot l] {F : ι → G → ℂ} {H : G → ℂ}
    (hF : ∀ᶠ i in l, IsPositiveDefiniteSub (F i))
    (hlim : ∀ x : G, Tendsto (fun i => F i x) l (𝓝 (H x))) :
    IsPositiveDefiniteSub H :=
  isPositiveDefiniteSub_iff_isPositiveDefinite.mpr
    (IsPositiveDefinite.of_tendsto (hF.mono fun _ hi => hi.isPositiveDefinite)
      fun a => hlim (WithNegStar.ofNegStar a))

/-! ### A.7. Normalization -/

/-- Multiplying a positive-definite function by the reciprocal of its real value at the origin
preserves positive definiteness. -/
lemma normalize (hF : IsPositiveDefiniteSub F) :
    IsPositiveDefiniteSub fun x => (((F 0).re)⁻¹ : ℂ) * F x :=
  isPositiveDefiniteSub_iff_isPositiveDefinite.mpr (by
    simpa using hF.isPositiveDefinite.normalize)

/-- The normalized function has value `1` at the origin. -/
@[simp]
lemma normalize_apply_zero (hF : IsPositiveDefiniteSub F) (h0 : F 0 ≠ 0) :
    (((F 0).re)⁻¹ : ℂ) * F 0 = 1 := by
  have hpos := hF.map_zero_re_pos_of_ne_zero h0
  rw [hF.map_zero_eq_ofReal_re]
  norm_cast
  exact inv_mul_cancel₀ hpos.ne'

/-- A normalized positive-definite function is bounded by `1`. -/
lemma norm_normalize_apply_le_one (hF : IsPositiveDefiniteSub F) (a : G) :
    ‖(((F 0).re)⁻¹ : ℂ) * F a‖ ≤ 1 := by
  simpa using hF.isPositiveDefinite.norm_normalize_apply_le_one_of_star_eq_neg
    (WithNegStar.toNegStar a) rfl

end IsPositiveDefiniteSub

/-! ### A.8. Continuity -/

namespace IsPositiveDefiniteSub

variable {G : Type*} [SeminormedAddCommGroup G] {F : G → ℂ}

/-- A positive-definite function on a seminormed additive commutative group is uniformly
continuous as soon as it is continuous at the origin. -/
lemma uniformContinuous_of_continuousAt_zero (hF : IsPositiveDefiniteSub F)
    (hcont : ContinuousAt F 0) : UniformContinuous F :=
  hF.isPositiveDefinite.uniformContinuous_of_continuousAt_zero_of_forall_star_eq_neg
    (fun _ => rfl) hcont

/-- A positive-definite function on a seminormed additive commutative group is continuous as soon
as it is continuous at the origin. -/
lemma continuous_of_continuousAt_zero (hF : IsPositiveDefiniteSub F)
    (hcont : ContinuousAt F 0) : Continuous F :=
  (hF.uniformContinuous_of_continuousAt_zero hcont).continuous

end IsPositiveDefiniteSub

/-- A nonnegative real constant is a positive-definite function. -/
lemma isPositiveDefiniteSub_const {k : ℂ} (hk : 0 ≤ k) :
    IsPositiveDefiniteSub (fun _ : G => k) :=
  isPositiveDefiniteSub_iff_isPositiveDefinite.mpr (isPositiveDefinite_const hk)

/-- The zero function is positive definite. -/
lemma isPositiveDefiniteSub_zero : IsPositiveDefiniteSub (fun _ : G => (0 : ℂ)) :=
  isPositiveDefiniteSub_const le_rfl

end TauCeti
