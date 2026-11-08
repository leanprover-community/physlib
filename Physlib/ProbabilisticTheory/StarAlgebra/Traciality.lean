/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Algebra.Star.Module
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Tactic.LinearCombination

/-!
# Tracial functionals

A functional on an algebra is tracial if the order of a product does not change its value.

## i. Overview

A functional `f` on an algebra is tracial if `f (x y) = f (y x)` for all `x` and `y`. The order
of a product does not change its value.

On an algebra with an adjoint it is enough to check `f (x⋆ x) = f (x x⋆)`. An operator and its
adjoint then give the same value in both orders.

## ii. Key results

- `LinearMap.IsTracial` : a complex-linear functional with `f (x * y) = f (y * x)`.
- `LinearMap.isTracial_iff_star_mul_self_eq_mul_star_self` : `f` is tracial if and only if
  `f (x⋆ * x) = f (x * x⋆)` for all `x`.

## iii. Table of contents

- A. Tracial functionals
- B. Checking on `x⋆ x`

## iv. References

-/

@[expose] public section

namespace LinearMap

variable {𝒜 : Type*} [NonUnitalNonAssocSemiring 𝒜] [Module ℂ 𝒜]

/-!

## A. Tracial functionals

-/

/-- A complex-linear functional is tracial if `f (x * y) = f (y * x)` for all `x` and `y`. -/
def IsTracial (f : 𝒜 →ₗ[ℂ] ℂ) : Prop :=
  ∀ x y : 𝒜, f (x * y) = f (y * x)

/-!

## B. Checking on `x⋆ x`

Apply the hypothesis to `x⋆ + y` and `x⋆ + i y`. The cross terms leave `C - C' = 0` and
`C + C' = 0` for the commutators `C = f [x, y]` and `C' = f [x⋆, y⋆]`, so `C = 0`.

-/

variable [StarRing 𝒜] [IsScalarTower ℂ 𝒜 𝒜] [SMulCommClass ℂ 𝒜 𝒜] [StarModule ℂ 𝒜]

/-- A functional is tracial if and only if `f (x⋆ x) = f (x x⋆)` for all `x`. -/
lemma isTracial_iff_star_mul_self_eq_mul_star_self (f : 𝒜 →ₗ[ℂ] ℂ) :
    f.IsTracial ↔ ∀ x : 𝒜, f (star x * x) = f (x * star x) := by
  constructor
  · intro ht x
    exact ht (star x) x
  intro h x y
  have h0 := h (star x)
  have h1 := h y
  have h2 := h (star x + y)
  have h3 := h (star x + Complex.I • y)
  simp only [star_add, star_star, star_smul, map_add, map_smul, mul_add, add_mul,
    smul_mul_assoc, mul_smul_comm, smul_eq_mul, Complex.star_def, Complex.conj_I] at h0 h1 h2 h3
  linear_combination (h2 - h0 - h1) / 2 - Complex.I / 2 *
    (h3 - h0 - h1 + (f (star y * y) - f (y * star y)) * Complex.I_mul_I) +
    (f (x * y) - f (y * x) + (f (star x * star y) - f (star y * star x))) / 2 * Complex.I_mul_I

end LinearMap
