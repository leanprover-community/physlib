/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import Mathlib.Basic.Complex.Basic
public import Physlib.Mathematics.Modules.ConjModule
public import Mathlib.Algebra.Star.Module
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.MvPowerSeries.Derivative
/-!

# The spacetime algebra

## i. Overview

The spacetime algebra `SpaceTimeAlgebra` is the ring of formal power series with complex
coefficients in four variables, one for each spacetime direction. The value at the base point of
an iterated partial derivative of a series is the corresponding coefficient multiplied by a
factorial. Consequently, a series is determined by these derivative values, and every family of
values arises from exactly one series.

## ii. Key results

- `SpaceTimeAlgebra` : formal power series in the spacetime directions.
- `SpaceTimeAlgebra.iteratedPDeriv` : iterated formal partial derivatives.
- `SpaceTimeAlgebra.constantCoeff_iteratedPDeriv` : derivative values are `s!` times coefficients.
- `SpaceTimeAlgebra.ext_of_constantCoeff_iteratedPDeriv` : derivative values determine a series.
- `SpaceTimeAlgebra.ofDerivValues` : the series with given derivative values.
- `SpaceTimeAlgebra.ofDerivValues_constantCoeff_iteratedPDeriv` : Taylor's formula.
- `SpaceTimeAlgebra.derivValuesEquiv` : series and derivative values are linearly equivalent.

## iii. Table of contents

- A. The spacetime algebra
- B. Iterated formal partial derivatives
  - B.1. Commutation of formal partial derivatives
  - B.2. Base-point values of iterated derivatives
- C. Series with equal derivative values
- D. Series from derivative values
  - D.1. Series with prescribed derivative values
  - D.2. The linear equivalence

## iv. References

* P. Haukkanen, Formal power series in several variables, Notes on Number Theory and Discrete
  Mathematics 25 (2019) 44–57, Section 4, Definitions 4.1–4.2 and Theorem 4.1, p. 48.
  https://doi.org/10.7546/nntdm.2019.25.4.44-57 [ref: haukkanen_2019_formal_power_series]
* I. Kolář, P. W. Michor and J. Slovák, Natural Operations in Differential Geometry,
  Sections 12.5–12.6 and 12.18, for the interpretation of Taylor series as coordinate
  expressions of jets. https://www.mat.univie.ac.at/~michor/kmsbookh.pdf
  [ref: kolar_michor_slovak_1993]
-/

@[expose] public section

/-!

## A. The spacetime algebra

The four spacetime directions are indexed by `Fin 1 ⊕ Fin 3`, with `Sum.inl 0` the time direction
and `Sum.inr i` the three space directions. The spacetime algebra has one variable `x^μ` for each
direction `μ`.

These power series are formal, meaning that a series is an arbitrary family of complex
coefficients, one for each monomial, and no convergence condition is imposed.

The formal variables represent coordinate displacements from a fixed, implicit spacetime point, the
base point. The constant coefficient represents the field value at that point. In differential
geometry, the data of all derivatives of a smooth map at a point is called its infinite-order jet
at that point (a mathematical notion, unrelated to jets in collider physics). In fixed coordinates,
the infinite-order jet of a smooth complex-valued field at the base point is recorded by the
series of its Taylor coefficients, which is an element of the spacetime algebra.

-/

/-- Formal power series in the four spacetime directions, with complex coefficients. -/
abbrev SpaceTimeAlgebra : Type := MvPowerSeries (Fin 1 ⊕ Fin 3) ℂ

namespace SpaceTimeAlgebra

open MvPowerSeries

/-!

## B. Iterated formal partial derivatives

### B.1. Commutation of formal partial derivatives

`pderiv μ` differentiates a series term by term with the power rule in `x^μ`, treating the other
variables as constants. Formal partial derivatives in different directions commute, so an iterated
derivative depends only on how many times each direction occurs. We therefore index iterated
derivatives by a multiset `s` of directions (an unordered list in which repetition is allowed) and
write `∂^s f` for `iteratedPDeriv s f`. For example, the multiset containing `μ` twice and `ν` once
gives `∂_μ ∂_μ ∂_ν f`.

-/

/-- Formal partial derivatives commute. -/
lemma pderiv_comm (μ ν : Fin 1 ⊕ Fin 3) (f : SpaceTimeAlgebra) :
    pderiv μ (pderiv ν f) = pderiv ν (pderiv μ f) := by
  classical
  ext m
  rcases eq_or_ne μ ν with rfl | h
  · rfl
  · simp only [coeff_pderiv, Finsupp.add_apply, Finsupp.single_eq_of_ne h,
      Finsupp.single_eq_of_ne h.symm, add_zero, add_right_comm m]
    ring

/-- Formal partial differentiation can be iterated over a multiset of directions. -/
instance : RightCommutative (fun (f : SpaceTimeAlgebra) (μ : Fin 1 ⊕ Fin 3) => pderiv μ f) where
  right_comm f μ ν := pderiv_comm ν μ f

/-- The iterated formal partial derivative `∂^s f`, differentiating once along each element of
  `s`. -/
noncomputable def iteratedPDeriv (s : Multiset (Fin 1 ⊕ Fin 3)) (f : SpaceTimeAlgebra) :
    SpaceTimeAlgebra :=
  s.foldl (fun f μ => pderiv μ f) f

@[simp]
lemma iteratedPDeriv_zero (f : SpaceTimeAlgebra) : iteratedPDeriv 0 f = f := rfl

@[simp]
lemma iteratedPDeriv_cons (μ : Fin 1 ⊕ Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3))
    (f : SpaceTimeAlgebra) :
    iteratedPDeriv (μ ::ₘ s) f = iteratedPDeriv s (pderiv μ f) :=
  Multiset.foldl_cons _ _ _ _

@[simp]
lemma iteratedPDeriv_singleton (μ : Fin 1 ⊕ Fin 3) (f : SpaceTimeAlgebra) :
    iteratedPDeriv {μ} f = pderiv μ f := rfl

/-!

### B.2. Base-point values of iterated derivatives

For a power series in one variable, the `n`-th derivative at `0` is `n!` times the coefficient of
`xⁿ`. This section proves the analogue in several variables, on which the rest of the file is
built. We write `(∂^s f)(0)` for the constant coefficient of `∂^s f`, which is its value at the base
point where every `x^μ` is zero, and call the family `s ↦ (∂^s f)(0)` the base-point derivative
values of `f`. A multiset `s` determines the monomial `x^s`, containing each `x^μ` as often as `μ`
occurs in `s`, and the number `s!`, the product of the factorials of these multiplicities. Applying
`∂^s` turns `x^s` into the constant `s!`, while every other monomial ends up either zero or without
a constant term, so `(∂^s f)(0)` is `s!` times the coefficient of `x^s` in `f`.

-/

/-- The base-point value of `∂^s f` is `s!` times the coefficient of `x^s` in `f`. -/
lemma constantCoeff_iteratedPDeriv (s : Multiset (Fin 1 ⊕ Fin 3)) (f : SpaceTimeAlgebra) :
    constantCoeff (iteratedPDeriv s f) =
      ((∏ ν, (s.count ν).factorial : ℕ) : ℂ) * coeff (Multiset.toFinsupp s) f := by
  classical
  induction s using Multiset.induction_on generalizing f with
  | empty => simp [coeff_zero_eq_constantCoeff]
  | cons μ s ih =>
    have hfac : ∏ ν, ((μ ::ₘ s).count ν).factorial =
        (s.count μ + 1) * ∏ ν, (s.count ν).factorial := by
      rw [Fintype.prod_eq_mul_prod_compl μ, Fintype.prod_eq_mul_prod_compl μ,
        Multiset.count_cons_self, Nat.factorial_succ, mul_assoc]
      exact congrArg _ (congrArg _ (Finset.prod_congr rfl fun ν hν => by
        rw [Multiset.count_cons_of_ne (by simpa using hν)]))
    rw [iteratedPDeriv_cons, ih, coeff_pderiv, hfac, ← Multiset.singleton_add,
      Multiset.toFinsupp_add, Multiset.toFinsupp_singleton, add_comm (Finsupp.single μ 1),
      Multiset.toFinsupp_apply]
    push_cast
    ring

/-!

## C. Series with equal derivative values

Since `s!` is nonzero, the coefficient of `x^s` in `f` is `(∂^s f)(0)` divided by `s!`. Two series
with the same base-point derivative values therefore have the same coefficients, and so are
equal. Similarly, a series whose first derivatives all vanish is the constant series given by its
base-point value.

-/

/-- Series whose iterated derivatives have the same base-point values are equal. -/
lemma ext_of_constantCoeff_iteratedPDeriv {f g : SpaceTimeAlgebra}
    (h : ∀ s, constantCoeff (iteratedPDeriv s f) = constantCoeff (iteratedPDeriv s g)) :
    f = g := by
  classical
  ext m
  have hm := h (Finsupp.toMultiset m)
  rw [constantCoeff_iteratedPDeriv, constantCoeff_iteratedPDeriv,
    Finsupp.toMultiset_toFinsupp] at hm
  exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr
    (Finset.prod_ne_zero_iff.mpr fun _ _ => Nat.factorial_ne_zero _)) hm

/-- A series with vanishing first derivatives is constant. -/
lemma eq_C_of_pderiv_eq_zero {f : SpaceTimeAlgebra} (hf : ∀ μ, pderiv μ f = 0) :
    f = C (constantCoeff f) :=
  pderiv.ext (fun μ => by rw [hf μ, pderiv_C]) (by rw [constantCoeff_C])

/-!

## D. Series from derivative values

### D.1. Series with prescribed derivative values

A family `F` of complex numbers indexed by multisets defines the series `ofDerivValues F`, whose
coefficient of `x^s` is `F s` divided by `s!`. By B.2, its base-point derivative values are the
values of `F`. Applied to the base-point derivative values of a series `f`, this construction
returns `f`, which is Taylor's formula `f = Σ_s (∂^s f)(0) / s! · x^s` (Haukkanen, Theorem 4.1).

-/

/-- The series whose base-point derivative values are `F`. -/
noncomputable def ofDerivValues (F : Multiset (Fin 1 ⊕ Fin 3) → ℂ) : SpaceTimeAlgebra :=
  fun m => ((∏ ν, (m ν).factorial : ℕ) : ℂ)⁻¹ * F (Finsupp.toMultiset m)

lemma coeff_ofDerivValues (F : Multiset (Fin 1 ⊕ Fin 3) → ℂ) (m : (Fin 1 ⊕ Fin 3) →₀ ℕ) :
    coeff m (ofDerivValues F) =
      ((∏ ν, (m ν).factorial : ℕ) : ℂ)⁻¹ * F (Finsupp.toMultiset m) :=
  rfl

/-- The base-point derivative values of `ofDerivValues F` are `F`. -/
lemma constantCoeff_iteratedPDeriv_ofDerivValues (F : Multiset (Fin 1 ⊕ Fin 3) → ℂ)
    (s : Multiset (Fin 1 ⊕ Fin 3)) :
    constantCoeff (iteratedPDeriv s (ofDerivValues F)) = F s := by
  have hs : ((∏ ν, (s.count ν).factorial : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun _ _ => Nat.factorial_ne_zero _)
  simp only [constantCoeff_iteratedPDeriv, coeff_ofDerivValues, Multiset.toFinsupp_apply,
    Multiset.toFinsupp_toMultiset, ← mul_assoc, mul_inv_cancel₀ hs, one_mul]

/-- A series is recovered from its base-point derivative values by `ofDerivValues`. -/
lemma ofDerivValues_constantCoeff_iteratedPDeriv (f : SpaceTimeAlgebra) :
    ofDerivValues (fun s => constantCoeff (iteratedPDeriv s f)) = f :=
  ext_of_constantCoeff_iteratedPDeriv fun s => constantCoeff_iteratedPDeriv_ofDerivValues _ s

/-!

### D.2. The linear equivalence

The two constructions are mutually inverse and `ℂ`-linear, so together they form the linear
equivalence `derivValuesEquiv` between the spacetime algebra and `Multiset (Fin 1 ⊕ Fin 3) → ℂ`.

-/

/-- The linear equivalence between series and their base-point derivative values. -/
noncomputable def derivValuesEquiv : SpaceTimeAlgebra ≃ₗ[ℂ] (Multiset (Fin 1 ⊕ Fin 3) → ℂ) :=
  LinearEquiv.symm
    { toFun := ofDerivValues
      map_add' F G := by ext m; simp [coeff_ofDerivValues, mul_add]
      map_smul' c F := by ext m; simp [coeff_ofDerivValues, mul_left_comm]
      invFun f s := constantCoeff (iteratedPDeriv s f)
      left_inv F := funext (constantCoeff_iteratedPDeriv_ofDerivValues F)
      right_inv := ofDerivValues_constantCoeff_iteratedPDeriv }

@[simp]
lemma derivValuesEquiv_apply (f : SpaceTimeAlgebra) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    derivValuesEquiv f s = constantCoeff (iteratedPDeriv s f) := rfl

@[simp]
lemma derivValuesEquiv_symm_apply (F : Multiset (Fin 1 ⊕ Fin 3) → ℂ) :
    derivValuesEquiv.symm F = ofDerivValues F := rfl


/-!

## Branch applications: star, Leibniz, and truncation

-/

/-!### A.1. The star structure on the jet ring

The star operation on the jet ring is coefficientwise complex conjugation, fixing
the formal variables. In particular the spacetime coordinates are self-adjoint.

-/

open MvPowerSeries

instance : Star SpaceTimeAlgebra where
  star f := fun n => star (f n)

@[simp]
lemma coeff_star (n : (Fin 1 ⊕ Fin 3) →₀ ℕ) (f : SpaceTimeAlgebra) :
    coeff n (star f) = star (coeff n f) := rfl

instance : StarRing SpaceTimeAlgebra where
  star_involutive f := funext fun n => star_star (f n)
  star_add f g := funext fun n => star_add (f n) (g n)
  star_mul f g := by
    have h : ∀ a b : SpaceTimeAlgebra, star (a * b) = star a * star b := by
      intro a b
      ext n
      classical
      rw [coeff_star, coeff_mul, coeff_mul, star_sum]
      exact Finset.sum_congr rfl fun p _ => by rw [star_mul', coeff_star, coeff_star]
    rw [h, mul_comm]

/-- Real scalars commute with the coefficientwise conjugation. -/
instance : StarModule ℝ SpaceTimeAlgebra where
  star_smul r f := funext fun n => star_smul r (f n)

/-- Complex scalars conjugate under the coefficientwise conjugation. -/
instance : StarModule ℂ SpaceTimeAlgebra where
  star_smul c f := funext fun n => star_smul c (f n)

@[simp]
lemma constantCoeff_star (f : SpaceTimeAlgebra) :
    constantCoeff (star f) = star (constantCoeff f) := rfl

@[simp]
lemma star_C (a : ℂ) :
    star (C a : SpaceTimeAlgebra) = C (star a) := by
  ext n
  classical
  rw [coeff_star, coeff_C, coeff_C]
  split_ifs <;> simp

/-- **The real structure of the jet ring.** Coefficientwise conjugation is a `ℂ`-linear
equivalence from the conjugate module of the jet ring back to the jet ring itself. It is
honestly `ℂ`-linear, not merely semilinear, because the conjugate-linearity of `star`
cancels against the twisted scalar action of `ConjModule`.

This is what identifies the jets of a conjugate field with the conjugates of the jets:
`ConjModule (SpaceTimeAlgebra ⊗[ℂ] V)` and `SpaceTimeAlgebra ⊗[ℂ] ConjModule V` differ
exactly by this equivalence on the jet-ring factor. -/
noncomputable def starConjEquiv : ConjModule SpaceTimeAlgebra ≃ₗ[ℂ] SpaceTimeAlgebra :=
  (conjEquiv (k := ℂ) (M := SpaceTimeAlgebra)).symm.trans (starLinearEquiv ℂ)

@[simp]
lemma starConjEquiv_apply (f : ConjModule SpaceTimeAlgebra) :
    starConjEquiv f = star ((conjEquiv (k := ℂ) (M := SpaceTimeAlgebra)).symm f) := rfl

@[simp]
lemma starConjEquiv_symm_apply (f : SpaceTimeAlgebra) :
    starConjEquiv.symm f = conjEquiv (k := ℂ) (M := SpaceTimeAlgebra) (star f) := rfl


/-- The first-order Leibniz rule: the degree-one Taylor coefficient, in the
  direction `μ`, of a product of jets. This is the coefficient-level statement
  that the first jet of a product is given by the product rule. -/
lemma coeff_single_one_mul (μ : Fin 1 ⊕ Fin 3) (f g : SpaceTimeAlgebra) :
    coeff (Finsupp.single μ 1) (f * g) =
      coeff (Finsupp.single μ 1) f * constantCoeff g +
        constantCoeff f * coeff (Finsupp.single μ 1) g := by
  classical
  rw [coeff_mul, Finsupp.antidiagonal_single,
    show Finset.antidiagonal (1 : ℕ) = {(0, 1), (1, 0)} by decide, Finset.map_insert,
    Finset.map_singleton, Finset.sum_insert (by simp [Finsupp.single_eq_zero]),
    Finset.sum_singleton]
  simp only [Function.Embedding.coe_prodMap, Function.Embedding.coeFn_mk, Prod.map_apply,
    Finsupp.single_zero, coeff_zero_eq_constantCoeff]
  ring

/-- The constant-coefficient evaluation of a jet, as a `ℂ`-linear map. -/
noncomputable def constantCoeffₗ : SpaceTimeAlgebra →ₗ[ℂ] ℂ where
  toFun := constantCoeff
  map_add' f g := by simp
  map_smul' c f := by simp [smul_eq_C_mul]

@[simp]
lemma constantCoeffₗ_apply (f : SpaceTimeAlgebra) : constantCoeffₗ f = constantCoeff f := rfl

/-!

### A.2. The formal partial derivative on the jet ring

-/

/-- The formal partial derivative commutes with the coefficientwise star. -/
lemma pderiv_star (ν : Fin 1 ⊕ Fin 3) (f : SpaceTimeAlgebra) :
    pderiv ν (star f) = star (pderiv ν f) := by
  ext s
  rw [coeff_pderiv, coeff_star, coeff_star, coeff_pderiv, star_mul']
  congr 1
  simp

/-- Iterated formal derivatives commute with a single formal partial derivative. -/
lemma iteratedPDeriv_pderiv (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
    (f : SpaceTimeAlgebra) :
    iteratedPDeriv s (pderiv μ f) = pderiv μ (iteratedPDeriv s f) := by
  induction s using Multiset.induction_on generalizing f with
  | empty => simp
  | cons ν s ih =>
      rw [iteratedPDeriv_cons, iteratedPDeriv_cons, pderiv_comm, ih]


/-- The iterated formal derivative is additive. -/
lemma iteratedPDeriv_add (s : Multiset (Fin 1 ⊕ Fin 3)) (f g : SpaceTimeAlgebra) :
    iteratedPDeriv s (f + g) = iteratedPDeriv s f + iteratedPDeriv s g := by
  induction s using Multiset.induction_on generalizing f g with
  | empty => rfl
  | cons μ t ih => rw [iteratedPDeriv_cons, iteratedPDeriv_cons, iteratedPDeriv_cons,
      map_add, ih]

/-- Iterated formal derivatives preserve complex scalar multiplication. -/
lemma iteratedPDeriv_smul (s : Multiset (Fin 1 ⊕ Fin 3)) (c : ℂ)
    (f : SpaceTimeAlgebra) :
    iteratedPDeriv s (c • f) = c • iteratedPDeriv s f := by
  induction s using Multiset.induction_on generalizing f with
  | empty => rfl
  | cons μ s ih => rw [iteratedPDeriv_cons, iteratedPDeriv_cons, Derivation.map_smul, ih]

/-- Iterated formal derivatives commute with negation. -/
lemma iteratedPDeriv_neg (s : Multiset (Fin 1 ⊕ Fin 3)) (f : SpaceTimeAlgebra) :
    iteratedPDeriv s (-f) = -iteratedPDeriv s f := by
  induction s using Multiset.induction_on generalizing f with
  | empty => rfl
  | cons μ s ih => rw [iteratedPDeriv_cons, iteratedPDeriv_cons, map_neg, ih]

/-- The iterated formal derivative of the zero jet vanishes. -/
@[simp]
lemma iteratedPDeriv_zero_apply (s : Multiset (Fin 1 ⊕ Fin 3)) :
    iteratedPDeriv s (0 : SpaceTimeAlgebra) = 0 := by
  induction s using Multiset.induction_on with
  | empty => rfl
  | cons μ t ih => rw [iteratedPDeriv_cons, map_zero, ih]

/-- The iterated formal derivative of a finite sum. -/
lemma iteratedPDeriv_sum {κ : Type*} (s : Multiset (Fin 1 ⊕ Fin 3)) (t : Finset κ)
    (f : κ → SpaceTimeAlgebra) :
    iteratedPDeriv s (∑ k ∈ t, f k)
      = ∑ k ∈ t, iteratedPDeriv s (f k) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih => rw [Finset.sum_insert ha, iteratedPDeriv_add, ih,
      Finset.sum_insert ha]

/-- The all-orders Leibniz rule for the iterated formal derivative on the jet ring:
  the derivative of a product distributes over the antidiagonal of the multiset of
  directions. -/
lemma iteratedPDeriv_mul (s : Multiset (Fin 1 ⊕ Fin 3)) (f g : SpaceTimeAlgebra) :
    iteratedPDeriv s (f * g)
      = (s.antidiagonal.map fun p =>
          iteratedPDeriv p.1 f * iteratedPDeriv p.2 g).sum := by
  induction s using Multiset.induction_on generalizing f g with
  | empty => simp [Multiset.antidiagonal_zero]
  | cons μ t ih =>
    rw [iteratedPDeriv_cons,
      show pderiv μ (f * g) = pderiv μ f * g + f * pderiv μ g from by
        rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, add_comm, mul_comm g],
      iteratedPDeriv_add, ih, ih,
      Multiset.map_congr rfl (fun p hp => by
        rw [show iteratedPDeriv p.1 (pderiv μ f)
            = iteratedPDeriv (μ ::ₘ p.1) f from
          (iteratedPDeriv_cons _ _ _).symm]),
      show (t.antidiagonal.map fun p =>
          iteratedPDeriv p.1 f * iteratedPDeriv p.2 (pderiv μ g)).sum
        = (t.antidiagonal.map fun p =>
          iteratedPDeriv p.1 f * iteratedPDeriv (μ ::ₘ p.2) g).sum from
        congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => by
          rw [show iteratedPDeriv (μ ::ₘ p.2) g
            = iteratedPDeriv p.2 (pderiv μ g) from iteratedPDeriv_cons _ _ _])]
    simp only [Multiset.antidiagonal_cons, Multiset.map_add, Multiset.sum_add,
      Multiset.map_map, Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq]
    exact add_comm _ _

/-- The base-point Taylor coefficient of a product: the convolution of the base-point
  Taylor coefficients. -/
lemma constantCoeff_iteratedPDeriv_mul (s : Multiset (Fin 1 ⊕ Fin 3)) (f g : SpaceTimeAlgebra) :
    constantCoeff (iteratedPDeriv s (f * g))
      = (s.antidiagonal.map fun p =>
          constantCoeff (iteratedPDeriv p.1 f) *
            constantCoeff (iteratedPDeriv p.2 g)).sum := by
  rw [iteratedPDeriv_mul, map_multiset_sum, Multiset.map_map]
  exact congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => map_mul _ _ _)

/-- The iterated derivative of a constant jet vanishes for a nonempty multiset of
  directions. -/
lemma iteratedPDeriv_C_of_ne_zero {s : Multiset (Fin 1 ⊕ Fin 3)} (hs : s ≠ 0) (c : ℂ) :
    iteratedPDeriv s (C c : SpaceTimeAlgebra) = 0 := by
  obtain ⟨μ, hμ⟩ := Multiset.exists_mem_of_ne_zero hs
  obtain ⟨t, rfl⟩ := Multiset.exists_cons_of_mem hμ
  rw [iteratedPDeriv_cons, pderiv_C, iteratedPDeriv_zero_apply]

/-!

### Truncation of jets

-/
/-- The `n`-th truncation of a jet: the Taylor coefficients of total degree
  greater than `n` are set to zero. -/
noncomputable def truncation (n : ℕ) (f : SpaceTimeAlgebra) : SpaceTimeAlgebra :=
  fun m => if Finsupp.degree m ≤ n then f m else 0

@[simp]
lemma coeff_truncation_of_le {n : ℕ} {m : (Fin 1 ⊕ Fin 3) →₀ ℕ}
    (h : Finsupp.degree m ≤ n) (f : SpaceTimeAlgebra) :
    coeff m (truncation n f) = coeff m f := ite_eq_left h

@[simp]
lemma coeff_truncation_of_gt {n : ℕ} {m : (Fin 1 ⊕ Fin 3) →₀ ℕ}
    (h : n < Finsupp.degree m) (f : SpaceTimeAlgebra) :
    coeff m (truncation n f) = 0 := ite_eq_right (not_le.mpr h)

lemma truncation_add (n : ℕ) (f g : SpaceTimeAlgebra) :
    truncation n (f + g) = truncation n f + truncation n g := by
  ext m
  by_cases hm : Finsupp.degree m ≤ n
  · rw [coeff_truncation_of_le hm, map_add, map_add,
      coeff_truncation_of_le hm, coeff_truncation_of_le hm]
  · rw [coeff_truncation_of_gt (not_le.mp hm), map_add,
      coeff_truncation_of_gt (not_le.mp hm), coeff_truncation_of_gt (not_le.mp hm), add_zero]

@[simp]
lemma truncation_zero (n : ℕ) : truncation n (0 : SpaceTimeAlgebra) = 0 := by
  ext m
  by_cases hm : Finsupp.degree m ≤ n
  · rw [coeff_truncation_of_le hm]
  · rw [coeff_truncation_of_gt (not_le.mp hm), map_zero]

/-- Truncation fixes the identity: a constant series has its only nonzero Taylor
  coefficient in degree zero, which every truncation keeps. -/
@[simp]
lemma truncation_one (n : ℕ) : truncation n (1 : SpaceTimeAlgebra) = 1 := by
  ext m
  by_cases hm : Finsupp.degree m ≤ n
  · rw [coeff_truncation_of_le hm]
  · rw [coeff_truncation_of_gt (not_le.mp hm), coeff_one,
      ite_eq_right (by rintro rfl; simp at hm)]

/-- A power series with value `1` and no coefficients in nonzero degree up to `n`
  truncates to `1`. -/
lemma truncation_eq_one_of_coeff {n : ℕ} {f : SpaceTimeAlgebra} (h0 : constantCoeff f = 1)
    (hf : ∀ p : (Fin 1 ⊕ Fin 3) →₀ ℕ, p ≠ 0 → Finsupp.degree p ≤ n → coeff p f = 0) :
    SpaceTimeAlgebra.truncation n f = SpaceTimeAlgebra.truncation n (1 : SpaceTimeAlgebra) := by
  ext m
  by_cases hm : Finsupp.degree m ≤ n
  · rw [SpaceTimeAlgebra.coeff_truncation_of_le hm, SpaceTimeAlgebra.coeff_truncation_of_le hm]
    rcases eq_or_ne m 0 with rfl | hm0
    · simpa [coeff_zero_eq_constantCoeff] using h0
    · rw [hf m hm0 hm, coeff_one, ite_eq_right hm0]
  · rw [SpaceTimeAlgebra.coeff_truncation_of_gt (not_le.mp hm),
      SpaceTimeAlgebra.coeff_truncation_of_gt (not_le.mp hm)]

/-!

## The Euler operator toolkit

-/

/-- The formal coordinates of the jet ring are self-adjoint. -/
lemma star_X (ρ : Fin 1 ⊕ Fin 3) : star (X ρ : SpaceTimeAlgebra) = X ρ := by
  ext m
  rw [SpaceTimeAlgebra.coeff_star,
    show (X ρ : SpaceTimeAlgebra) = monomial (Finsupp.single ρ 1) 1 from rfl, coeff_monomial]
  split_ifs <;> simp

/-- The Taylor coefficients of a jet multiplied by a formal coordinate: the
  coefficient shifts down by one in that direction. -/
lemma coeff_X_smul (ρ : Fin 1 ⊕ Fin 3) (f : SpaceTimeAlgebra) (p : (Fin 1 ⊕ Fin 3) →₀ ℕ) :
    coeff p ((X ρ : SpaceTimeAlgebra) • f) =
      if Finsupp.single ρ 1 ≤ p then coeff (p - Finsupp.single ρ 1) f else 0 := by
  rw [smul_eq_mul, show (X ρ : SpaceTimeAlgebra) = monomial (Finsupp.single ρ 1) 1 from rfl,
    coeff_monomial_mul]
  split_ifs <;> simp

/-- The Euler (radial) operator acts on Taylor coefficients as multiplication by the
  total degree. -/
lemma coeff_sum_X_smul_pderiv (f : SpaceTimeAlgebra) (p : (Fin 1 ⊕ Fin 3) →₀ ℕ) :
    coeff p (∑ ρ, (X ρ : SpaceTimeAlgebra) • pderiv ρ f) =
      ((Finsupp.degree p : ℕ) : ℂ) * coeff p f := by
  classical
  rw [map_sum]
  have ht : ∀ ρ, coeff p ((X ρ : SpaceTimeAlgebra) • pderiv ρ f) = (p ρ : ℂ) * coeff p f := by
    intro ρ
    rw [coeff_X_smul]
    by_cases h : Finsupp.single ρ 1 ≤ p
    · have hρ : 1 ≤ p ρ := by simpa using Finsupp.single_le_iff.mp h
      rw [ite_eq_left h, coeff_pderiv, tsub_add_cancel_of_le h, Finsupp.coe_tsub, Pi.sub_apply,
        Finsupp.single_eq_same, Nat.cast_sub hρ]
      push_cast
      ring
    · have hρ : p ρ = 0 := by
        by_contra hc
        exact h (Finsupp.single_le_iff.mpr (by omega))
      rw [ite_eq_right h, hρ]
      simp
  rw [Finset.sum_congr rfl fun ρ _ => ht ρ, ← Finset.sum_mul, ← Nat.cast_sum,
    ← Finsupp.degree_eq_sum]

/-- The scalar vanishing principle for the Euler operator: a jet vanishing at the base
  point that is killed by the Euler operator is zero. -/
lemma eq_zero_of_sum_X_smul_pderiv_eq_zero {f : SpaceTimeAlgebra} (h0 : constantCoeff f = 0)
    (hf : ∑ ρ, (X ρ : SpaceTimeAlgebra) • pderiv ρ f = 0) : f = 0 := by
  ext p
  rcases eq_or_ne p 0 with rfl | hp
  · simpa [coeff_zero_eq_constantCoeff] using h0
  · have h := congrArg (coeff p) hf
    rw [coeff_sum_X_smul_pderiv, map_zero] at h
    have hne : ((Finsupp.degree p : ℕ) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr fun hc => hp ((Finsupp.degree_eq_zero_iff p).mp hc)
    simpa using (mul_eq_zero.mp h).resolve_left hne

/-!

### The Euler vanishing principle by degree

The graded form of `eq_zero_of_sum_X_smul_pderiv_eq_zero`: control of the first
derivatives below degree `n` controls the coefficients up to degree `n`.

-/

/-- A product with a factor whose coefficients vanish below degree `n` has coefficients
  vanishing below degree `n`. -/
lemma coeff_mul_eq_zero_of_lt {n : ℕ} {w : SpaceTimeAlgebra}
    (hw : ∀ q : (Fin 1 ⊕ Fin 3) →₀ ℕ, Finsupp.degree q < n → coeff q w = 0) (v : SpaceTimeAlgebra)
    {q : (Fin 1 ⊕ Fin 3) →₀ ℕ} (hq : Finsupp.degree q < n) : coeff q (w * v) = 0 := by
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun p hp => ?_
  have hpq : p.1 + p.2 = q := Finset.mem_antidiagonal.mp hp
  have hdeg : Finsupp.degree p.1 ≤ Finsupp.degree q := by
    rw [← hpq, map_add]
    exact Nat.le_add_right _ _
  rw [hw p.1 (lt_of_le_of_lt hdeg hq), zero_mul]

/-- The Euler vanishing principle: a power series all of whose first derivatives have
  coefficients vanishing below degree `n` has vanishing coefficients in every nonzero degree
  up to `n`, since `∑_ρ x_ρ ∂_ρ f` has the coefficient of `f` at `p` scaled by the degree
  of `p`. -/
lemma coeff_eq_zero_of_coeff_pderiv_eq_zero {n : ℕ} {f : SpaceTimeAlgebra}
    (hf : ∀ (ρ : Fin 1 ⊕ Fin 3) (q : (Fin 1 ⊕ Fin 3) →₀ ℕ), Finsupp.degree q < n →
      coeff q (pderiv ρ f) = 0)
    {p : (Fin 1 ⊕ Fin 3) →₀ ℕ} (hp : p ≠ 0) (hpn : Finsupp.degree p ≤ n) : coeff p f = 0 := by
  have h1 := SpaceTimeAlgebra.coeff_sum_X_smul_pderiv f p
  have h2 : coeff p (∑ ρ, (X ρ : SpaceTimeAlgebra) • pderiv ρ f) = 0 := by
    rw [map_sum]
    refine Finset.sum_eq_zero fun ρ _ => ?_
    rw [SpaceTimeAlgebra.coeff_X_smul]
    split_ifs with hle
    · refine hf ρ _ ?_
      have hd := congrArg Finsupp.degree (tsub_add_cancel_of_le hle)
      rw [map_add, Finsupp.degree_single] at hd
      omega
    · rfl
  rw [h2] at h1
  have hne : ((Finsupp.degree p : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr fun hc => hp ((Finsupp.degree_eq_zero_iff p).mp hc)
  exact (mul_eq_zero.mp h1.symm).resolve_left hne

/-- A power series satisfying a radial relation `∂_ρ f = x_ρ f`, with the `x_ρ` vanishing
  below degree `n`, has no coefficients in nonzero degree up to `n`. -/
lemma coeff_eq_zero_of_pderiv_eq_mul {n : ℕ} {f : SpaceTimeAlgebra}
    {x : (Fin 1 ⊕ Fin 3) → SpaceTimeAlgebra}
    (hd : ∀ ρ, pderiv ρ f = x ρ * f)
    (hx : ∀ (ρ : Fin 1 ⊕ Fin 3) (q : (Fin 1 ⊕ Fin 3) →₀ ℕ), Finsupp.degree q < n →
      coeff q (x ρ) = 0)
    {p : (Fin 1 ⊕ Fin 3) →₀ ℕ} (hp : p ≠ 0) (hpn : Finsupp.degree p ≤ n) : coeff p f = 0 :=
  coeff_eq_zero_of_coeff_pderiv_eq_zero
    (fun ρ q hq => by rw [hd ρ]; exact coeff_mul_eq_zero_of_lt (hx ρ) f hq) hp hpn

lemma C_real_smul (r : ℝ) (x : ℂ) :
    (MvPowerSeries.C (r • x) : SpaceTimeAlgebra) = r • MvPowerSeries.C x := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, MvPowerSeries.algebraMap_apply]

/-- The constant coefficient commutes with real scalars. -/
lemma constantCoeff_real_smul (r : ℝ) (f : SpaceTimeAlgebra) :
    MvPowerSeries.constantCoeff (r • f) = r • MvPowerSeries.constantCoeff f := by
  rw [← algebraMap_smul ℂ r, MvPowerSeries.constantCoeff_smul, algebraMap_smul]

/-- The formal derivatives commute with real scalars. -/
lemma pderiv_real_smul (μ : Fin 1 ⊕ Fin 3) (r : ℝ) (f : SpaceTimeAlgebra) :
    MvPowerSeries.pderiv μ (r • f) = r • MvPowerSeries.pderiv μ f := by
  rw [← algebraMap_smul ℂ r, Derivation.map_smul, algebraMap_smul]


end SpaceTimeAlgebra
