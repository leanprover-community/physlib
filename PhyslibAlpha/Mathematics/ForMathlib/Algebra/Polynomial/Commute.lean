/-
Copyright (c) 2026 Jinzheng Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import Mathlib.Algebra.Polynomial.Coeff
/-!
# Commuting and anticommuting polynomials

Polynomials over a noncommutative ring commute, or anticommute, when their coefficients do.

## i. Overview

Over a noncommutative ring the polynomials are themselves noncommutative. The coefficient of
`X ^ n` in `p * q` is the sum over the antidiagonal of `p.coeff a * q.coeff b`, and in `q * p` it
is the same sum with the factors in the opposite order. So two polynomials commute as soon as
each coefficient of the one commutes with each coefficient of the other, and they anticommute as
soon as the coefficients pairwise anticommute.

## ii. Key results

- `Polynomial.commute_of_commute_coeff` : polynomials with pairwise commuting coefficients
  commute.
- `Polynomial.mul_eq_neg_mul_of_coeff` : polynomials with pairwise anticommuting coefficients
  anticommute.

## iii. Table of contents

- A. Commuting and anticommuting coefficients

## iv. References

* None.

-/

@[expose] public section

namespace Polynomial

/-!

## A. Commuting and anticommuting coefficients

-/

/-- Two polynomials commute as soon as each coefficient of the one commutes with each
  coefficient of the other. The coefficients of the two products are the same sums over the
  antidiagonal, read in opposite orders. -/
lemma commute_of_commute_coeff {R : Type*} [Semiring R]
    {p q : Polynomial R} (h : ∀ a b, Commute (p.coeff a) (q.coeff b)) : Commute p q := by
  show p * q = q * p
  exact AddMonoidAlgebra.ext <| Finsupp.ext fun n => (Polynomial.coeff_mul p q n).trans
    ((Finset.sum_congr rfl fun x _ => (h x.1 x.2).eq).trans
      ((Finset.Nat.sum_antidiagonal_swap (f := fun x => q.coeff x.1 * p.coeff x.2)).trans
        (Polynomial.coeff_mul q p n).symm))

/-- Two polynomials anticommute as soon as each coefficient of the one anticommutes with
  each coefficient of the other. -/
lemma mul_eq_neg_mul_of_coeff {R : Type*} [Ring R] {p q : Polynomial R}
    (h : ∀ a b, p.coeff a * q.coeff b = -(q.coeff b * p.coeff a)) : p * q = -(q * p) :=
  AddMonoidAlgebra.ext <| Finsupp.ext fun n => (Polynomial.coeff_mul p q n).trans
    ((Finset.sum_congr rfl fun x _ => h x.1 x.2).trans
      ((Finset.sum_neg_distrib _).trans
        ((congrArg Neg.neg
          ((Finset.Nat.sum_antidiagonal_swap (f := fun x => q.coeff x.1 * p.coeff x.2)).trans
            (Polynomial.coeff_mul q p n).symm)).trans
          (Polynomial.coeff_neg (q * p) n).symm)))

end Polynomial
