/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.MinkowskiMatrix
/-!
# The Minkowski matrix over the integers

The Minkowski matrix with integer entries, so that the kernel can evaluate it.

## i. Overview

The entries of `minkowskiMatrix` are integers, but it is a matrix over `ℝ`, and the kernel
cannot evaluate arithmetic in `ℝ`. Statements which a decision procedure has to evaluate are
therefore stated with `minkowskiMatrixZ`, the same diagonal matrix `diag(1, -1, …, -1)` taken
over `ℤ`. The bridge back is `minkowskiMatrixZ.cast_apply`, which casts an entry to the
corresponding entry of `minkowskiMatrix`; the remaining lemmas are the entry values and the
symmetry, matching the `minkowskiMatrix` API.

## ii. Key results

- `minkowskiMatrixZ` : the Minkowski matrix over `ℤ`.
- `minkowskiMatrixZ.cast_apply` : its cast to `ℝ` is `minkowskiMatrix`, entry by entry.
- `minkowskiMatrixZ.inl_0_inl_0`, `minkowskiMatrixZ.inr_i_inr_i`,
  `minkowskiMatrixZ.off_diag_zero` : the entries.
- `minkowskiMatrixZ.comm` : it is symmetric.

## iii. Table of contents

- A. The Minkowski matrix over the integers

## iv. References

The real Minkowski matrix and its API are in `Physlib.Relativity.MinkowskiMatrix`.

-/

@[expose] public section

open Matrix

/-!

## A. The Minkowski matrix over the integers

-/

/-- The Minkowski matrix over the integers, `diag(1, -1, -1, ...)` in `ℤ`. Its cast to `ℝ` is
  `minkowskiMatrix`, by `minkowskiMatrixZ.cast_apply`. -/
def minkowskiMatrixZ {d : ℕ} : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℤ :=
  diagonal (Sum.elim 1 (-1))

namespace minkowskiMatrixZ

variable {d : ℕ}

/-- The integer Minkowski matrix as a diagonal matrix. -/
lemma as_diagonal : @minkowskiMatrixZ d = diagonal (Sum.elim 1 (-1)) := rfl

/-- The time-time component of the integer Minkowski matrix is `1`. -/
@[simp]
lemma inl_0_inl_0 : @minkowskiMatrixZ d (Sum.inl 0) (Sum.inl 0) = 1 := by
  simp [minkowskiMatrixZ]

/-- The space diagonal components of the integer Minkowski matrix are `-1`. -/
@[simp]
lemma inr_i_inr_i (i : Fin d) : @minkowskiMatrixZ d (Sum.inr i) (Sum.inr i) = -1 := by
  simp [minkowskiMatrixZ]

/-- The off-diagonal components of the integer Minkowski matrix vanish. -/
@[simp]
lemma off_diag_zero {μ ν : Fin 1 ⊕ Fin d} (h : μ ≠ ν) : @minkowskiMatrixZ d μ ν = 0 :=
  diagonal_apply_ne _ h

/-- The integer Minkowski matrix is symmetric, being diagonal. -/
lemma comm (μ ν : Fin 1 ⊕ Fin d) : @minkowskiMatrixZ d μ ν = minkowskiMatrixZ ν μ := by
  rcases eq_or_ne μ ν with rfl | h
  · rfl
  · rw [off_diag_zero h, off_diag_zero h.symm]

/-- The integer Minkowski matrix casts to the Minkowski matrix, entry by entry. -/
lemma cast_apply (μ ν : Fin 1 ⊕ Fin d) :
    ((minkowskiMatrixZ μ ν : ℤ) : ℝ) = minkowskiMatrix μ ν := by
  rcases eq_or_ne μ ν with rfl | h
  · match μ with
    | Sum.inl i => rw [Subsingleton.elim i 0]; simp
    | Sum.inr i => simp
  · rw [off_diag_zero h, minkowskiMatrix.off_diag_zero h]
    simp

end minkowskiMatrixZ
