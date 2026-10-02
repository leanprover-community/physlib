/-
Copyright (c) 2026 Giuseppe Sorge. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuseppe Sorge
-/
module

public import Mathlib.Data.Matrix.Mul
/-!

# Orthogonal matrices and the dot product

An orthogonal matrix — a square matrix `A` with `Aᵀ A = 1` — preserves the dot product of vectors,
and in particular their squared lengths. This is the algebraic content behind the
frame-independence of the *rotational* kinetic energy in rigid-body dynamics: rotating a velocity
does not change its speed.

-/

@[expose] public section

namespace Matrix

/-- An orthogonal matrix preserves the dot product: if `Aᵀ A = 1` then `(A v) ⬝ᵥ (A w) = v ⬝ᵥ w`.
Taking `w = v` shows orthogonal matrices preserve squared lengths, `(A v) ⬝ᵥ (A v) = v ⬝ᵥ v`. -/
lemma dotProduct_mulVec_orthogonal {R : Type*} [CommRing R] {n : Type*} [Fintype n]
    [DecidableEq n] {A : Matrix n n R} (hA : Aᵀ * A = 1) (v w : n → R) :
    (A *ᵥ v) ⬝ᵥ (A *ᵥ w) = v ⬝ᵥ w := by
  rw [dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec, hA, one_mulVec]

end Matrix
