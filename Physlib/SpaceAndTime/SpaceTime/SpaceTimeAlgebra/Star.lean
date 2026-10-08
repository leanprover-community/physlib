/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import Mathlib.LinearAlgebra.Complex.Module
public import Physlib.SpaceAndTime.SpaceTime.SpaceTimeAlgebra.Basic
/-!

# Complex conjugation in the spacetime algebra

The spacetime algebra is a star ring under complex conjugation of the Taylor coefficients.

## i. Overview

The star of a series in the spacetime algebra conjugates each of its complex coefficients and
fixes each coordinate variable `x^μ`. The Taylor coefficients of the complex conjugate of a smooth
field are the conjugates of its Taylor coefficients, so if `f` records a field at the base point
then `star f` records the conjugate field.

Conjugation is an involution that respects sums and products. It conjugates complex scalars, fixes
real scalars, and commutes with every iterated derivative `∂^s`.

## ii. Key results

- `SpaceTimeAlgebra.coeff_star` : the coefficients of `star f` are the conjugates of those of `f`.
- `SpaceTimeAlgebra.star_C` : conjugating a constant series conjugates the constant.
- `SpaceTimeAlgebra.star_X` : the coordinate variables are fixed by conjugation.
- `SpaceTimeAlgebra.pderiv_star` : conjugation commutes with formal partial derivatives.
- `SpaceTimeAlgebra.iteratedPDeriv_star` : conjugation commutes with iterated derivatives.

## iii. Table of contents

- A. Coefficientwise conjugation
  - A.1. The star ring structure
  - A.2. Constants and coordinates
  - A.3. Real and complex scalars
- B. Formal partial derivatives

## iv. References

* None.

-/

@[expose] public section

namespace SpaceTimeAlgebra

open MvPowerSeries

/-!

## A. Coefficientwise conjugation

The star is the coefficient map `map (starRingEnd ℂ)`. Since `SpaceTimeAlgebra` is an
abbreviation, these are instances on `MvPowerSeries (Fin 1 ⊕ Fin 3) ℂ`.

-/

/-- The star of a series in the spacetime algebra conjugates each of its coefficients. -/
instance : Star SpaceTimeAlgebra where
  star := map (starRingEnd ℂ)

@[simp]
lemma coeff_star (n : (Fin 1 ⊕ Fin 3) →₀ ℕ) (f : SpaceTimeAlgebra) :
    coeff n (star f) = star (coeff n f) := rfl

@[simp]
lemma constantCoeff_star (f : SpaceTimeAlgebra) :
    constantCoeff (star f) = star (constantCoeff f) := rfl

/-!

### A.1. The star ring structure

Since the spacetime algebra is commutative, a ring homomorphism that is an involution makes it a
star ring.

-/

/-- The spacetime algebra is a star ring under coefficientwise conjugation. -/
instance : StarRing SpaceTimeAlgebra where
  star_involutive f := ext fun n => star_star (coeff n f)
  star_mul f g := (map_mul (map (starRingEnd ℂ)) f g).trans (mul_comm _ _)
  star_add f g := map_add (map (starRingEnd ℂ)) f g

/-!

### A.2. Constants and coordinates

-/

@[simp]
lemma star_C (a : ℂ) : star (C a : SpaceTimeAlgebra) = C (star a) := map_C _ a

@[simp]
lemma star_X (μ : Fin 1 ⊕ Fin 3) : star (X μ : SpaceTimeAlgebra) = X μ := map_X _ μ

/-!

### A.3. Real and complex scalars

-/

/-- Conjugation fixes real scalars, `star (r • f) = r • star f`. -/
instance : StarModule ℝ SpaceTimeAlgebra where
  star_smul r f := ext fun n => star_smul r (coeff n f)

/-- Conjugation conjugates complex scalars, `star (c • f) = star c • star f`. -/
instance : StarModule ℂ SpaceTimeAlgebra where
  star_smul c f := ext fun n => star_smul c (coeff n f)

/-!

## B. Formal partial derivatives

The coefficient of `x^n` in `pderiv μ f` is the coefficient of `x^(n + single μ 1)` in `f` times
the natural number `n μ + 1`, which conjugation fixes.

-/

/-- Conjugation commutes with formal partial derivatives. -/
lemma pderiv_star (μ : Fin 1 ⊕ Fin 3) (f : SpaceTimeAlgebra) :
    pderiv μ (star f) = star (pderiv μ f) := by
  ext n
  simp [coeff_pderiv, star_mul']

/-- Conjugation commutes with iterated formal partial derivatives. -/
lemma iteratedPDeriv_star (s : Multiset (Fin 1 ⊕ Fin 3)) (f : SpaceTimeAlgebra) :
    iteratedPDeriv s (star f) = star (iteratedPDeriv s f) := by
  induction s using Multiset.induction_on generalizing f with
  | empty => rfl
  | cons μ s ih => rw [iteratedPDeriv_cons, iteratedPDeriv_cons, pderiv_star, ih]

end SpaceTimeAlgebra
