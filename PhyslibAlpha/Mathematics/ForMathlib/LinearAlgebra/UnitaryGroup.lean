/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Basic.Complex.Basic
/-!
# Diagonal matrices in the special unitary group

A criterion for a diagonal complex matrix to lie in the special unitary group.

## i. Overview

A diagonal matrix `diagonal d` is unitary exactly when each entry satisfies
`d i * star (d i) = 1`, and its determinant is the product of the entries. So a diagonal
matrix of unit scalars whose product is one lies in `specialUnitaryGroup n ℂ`. This is how
elements of a maximal torus of `SU(n)` are built.

## ii. Key results

- `Matrix.mem_specialUnitaryGroup_diagonal` : a diagonal matrix of unit scalars with product
  one lies in the special unitary group.

## iii. Table of contents

- A. Diagonal matrices in the special unitary group

## iv. References

- None.

-/

@[expose] public section

namespace Matrix

/-!

## A. Diagonal matrices in the special unitary group

-/

/-- A diagonal matrix whose entries are unit scalars with product one lies in the special
  unitary group. -/
lemma mem_specialUnitaryGroup_diagonal {n : Type*} [Fintype n] [DecidableEq n]
    (d : n → ℂ) (hd : ∀ i, d i * star (d i) = 1) (hdet : ∏ i, d i = 1) :
    Matrix.diagonal d ∈ Matrix.specialUnitaryGroup n ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    simp only [Pi.star_apply]
    rw [funext hd, Matrix.diagonal_one]
  · rw [Matrix.det_diagonal, hdet]

end Matrix
