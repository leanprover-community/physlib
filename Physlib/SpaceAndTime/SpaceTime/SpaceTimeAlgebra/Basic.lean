/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.MvPowerSeries.Derivative
/-!

# The spacetime algebra

## i. Overview

The spacetime algebra `SpaceTimeAlgebra` is the ring of formal power series with complex
coefficients in four variables, one for each spacetime direction. The value at the base point of
an iterated partial derivative of a series is the corresponding coefficient multiplied by a
factorial. Consequently, a series is determined by these derivative values, and every family of
values arises from exactly one series. Iterated derivatives of a product obey the all-orders
Leibniz rule.

## ii. Key results

- `SpaceTimeAlgebra` : formal power series in the spacetime directions.
- `SpaceTimeAlgebra.iteratedPDeriv` : iterated formal partial derivatives.
- `SpaceTimeAlgebra.constantCoeff_iteratedPDeriv` : derivative values are `s!` times coefficients.
- `SpaceTimeAlgebra.iteratedPDeriv_mul` : the all-orders Leibniz rule.
- `SpaceTimeAlgebra.ext_of_constantCoeff_iteratedPDeriv` : derivative values determine a series.
- `SpaceTimeAlgebra.ofDerivValues` : the series with given derivative values.
- `SpaceTimeAlgebra.ofDerivValues_constantCoeff_iteratedPDeriv` : Taylor's formula.
- `SpaceTimeAlgebra.derivValuesEquiv` : series and derivative values are linearly equivalent.

## iii. Table of contents

- A. The spacetime algebra
- B. Iterated formal partial derivatives
  - B.1. Commutation of formal partial derivatives
  - B.2. Base-point values of iterated derivatives
  - B.3. The Leibniz rule
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

lemma iteratedPDeriv_add (s : Multiset (Fin 1 ⊕ Fin 3)) (f g : SpaceTimeAlgebra) :
    iteratedPDeriv s (f + g) = iteratedPDeriv s f + iteratedPDeriv s g := by
  induction s using Multiset.induction_on generalizing f g with
  | empty => rfl
  | cons μ s ih => simp only [iteratedPDeriv_cons, map_add, ih]

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

### B.3. The Leibniz rule

To apply `∂^s` to `f g`, each direction in `s` acts on either `f` or `g`, so `∂^s (f g)` is a sum
of `(∂^t₁ f) (∂^t₂ g)` over the splits `t₁ + t₂ = s` in `Multiset.antidiagonal s`. Each split
appears once for every assignment of the elements of `s` that produces it, so repeated directions
give multiplicities: `∂_μ² (f g) = (∂_μ² f) g + 2 (∂_μ f) (∂_μ g) + f (∂_μ² g)`. The same formula
holds for base-point derivative values, but not for the Taylor coefficients, which are divided by
`s!`.

-/

/-- The all-orders Leibniz rule for iterated formal partial derivatives. -/
lemma iteratedPDeriv_mul (s : Multiset (Fin 1 ⊕ Fin 3)) (f g : SpaceTimeAlgebra) :
    iteratedPDeriv s (f * g) =
      (s.antidiagonal.map fun p => iteratedPDeriv p.1 f * iteratedPDeriv p.2 g).sum := by
  induction s using Multiset.induction_on generalizing f g with
  | empty => simp
  | cons μ s ih =>
    rw [iteratedPDeriv_cons, Derivation.leibniz, smul_eq_mul, smul_eq_mul, mul_comm g,
      iteratedPDeriv_add, ih, ih]
    simp [Multiset.map_map]

/-- The Leibniz rule for the base-point derivative values of a product. -/
lemma constantCoeff_iteratedPDeriv_mul (s : Multiset (Fin 1 ⊕ Fin 3)) (f g : SpaceTimeAlgebra) :
    constantCoeff (iteratedPDeriv s (f * g)) =
      (s.antidiagonal.map fun p =>
        constantCoeff (iteratedPDeriv p.1 f) * constantCoeff (iteratedPDeriv p.2 g)).sum := by
  simp [iteratedPDeriv_mul, map_multiset_sum, Multiset.map_map]

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

end SpaceTimeAlgebra
