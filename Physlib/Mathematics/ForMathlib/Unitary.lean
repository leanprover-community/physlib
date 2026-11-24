/-
Copyright (c) 2026 Daniel Leonforte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Leonforte
-/
module

public import Mathlib.Algebra.Star.Unitary

/-!

# Self-adjoint involutions are unitary

## i. Overview

A self-adjoint element `u` of a star monoid with `u * u = 1` is unitary, since then
`star u * u = u * star u = u * u = 1`.

## ii. Key results

- `IsSelfAdjoint.mem_unitary_of_mul_self` : a self-adjoint involution is unitary.

## iii. Table of contents

- A. Self-adjoint involutions

## iv. References

* None.

-/

@[expose] public section

/-!

## A. Self-adjoint involutions

-/

/-- A self-adjoint element `u` with `u * u = 1` is unitary. -/
lemma IsSelfAdjoint.mem_unitary_of_mul_self {R : Type*} [Monoid R] [StarMul R] {u : R}
    (hu : IsSelfAdjoint u) (h : u * u = 1) : u ∈ unitary R := by
  rw [Unitary.mem_iff, hu.star_eq]
  exact ⟨h, h⟩
