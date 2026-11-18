/-
Copyright (c) 2026 Chengyuan AI Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qianli Ma
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Compression by a projection operator

Compression sandwiches an operator between two copies of a projection.

## i. Overview

A star projection is a self-adjoint idempotent. For a star projection `p`, compression
takes an operator `a` to `p * a * p`. On a Hilbert space this specializes to the
sandwich formed from a submodule's orthogonal projection.

## ii. Key results

- `IsStarProjection.compress` is the compression by a star projection.
- `IsStarProjection.compress_mul_compress` gives the product of two compressed operators.
- `Submodule.starProjection_compress_eq_comp` identifies the abstract compression with the
  composition of bounded operators.

## iii. Table of contents

- A. Algebraic compression
- B. Compression on a Hilbert space

## iv. References

* None.
-/

@[expose] public section

/-!
## A. Algebraic compression
-/

namespace IsStarProjection

variable {A : Type*} {p : A}

/-- Compression of `a` by a star projection `p`, given by `p * a * p`. -/
def compress [Mul A] [Star A] (_hp : IsStarProjection p) (a : A) : A :=
  p * a * p

section Semigroup

variable [Semigroup A] [Star A] (hp : IsStarProjection p)

/-- Multiplying a compression by its projection on the left leaves it unchanged. -/
@[simp] lemma mul_compress (a : A) : p * hp.compress a = hp.compress a := by
  have hpp : p * p = p := hp.isIdempotentElem
  simp only [compress, ← mul_assoc, hpp]

/-- Multiplying a compression by its projection on the right leaves it unchanged. -/
@[simp] lemma compress_mul (a : A) : hp.compress a * p = hp.compress a := by
  have hpp : p * p = p := hp.isIdempotentElem
  simp only [compress, mul_assoc, hpp]

/-- Compression by the same projection twice is the same as compression once. -/
@[simp] lemma compress_compress (a : A) : hp.compress (hp.compress a) = hp.compress a := by
  change p * hp.compress a * p = hp.compress a
  rw [hp.mul_compress, hp.compress_mul]

/-- The product of two compressions can be written as a single compression with an
intermediate projection. -/
lemma compress_mul_compress (a b : A) :
    hp.compress a * hp.compress b = hp.compress (a * p * b) := by
  have hpp : p * p = p := hp.isIdempotentElem
  unfold compress
  calc
    p * a * p * (p * b * p) = p * (a * (p * p) * b) * p := by simp only [mul_assoc]
    _ = _ := by rw [hpp]

end Semigroup

section Semiring

variable [NonUnitalSemiring A] [Star A] (hp : IsStarProjection p)

@[simp] lemma compress_zero : hp.compress 0 = 0 := by
  simp [compress]

lemma compress_add (a b : A) : hp.compress (a + b) = hp.compress a + hp.compress b := by
  simp only [compress, mul_add, add_mul]

end Semiring

section Star

variable [Semigroup A] [StarMul A] (hp : IsStarProjection p)

/-- Compression commutes with taking the adjoint. -/
lemma star_compress (a : A) : star (hp.compress a) = hp.compress (star a) := by
  simp only [compress, star_mul, hp.isSelfAdjoint.star_eq, mul_assoc]

/-- Compressing a self-adjoint operator gives a self-adjoint operator. -/
lemma isSelfAdjoint_compress {a : A} (ha : IsSelfAdjoint a) : IsSelfAdjoint (hp.compress a) := by
  exact ha.conjugate_self hp.isSelfAdjoint

end Star

end IsStarProjection

/-!
## B. Compression on a Hilbert space
-/

namespace Submodule

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- Compressing by a submodule's orthogonal projection is the corresponding composition
of bounded operators. -/
lemma starProjection_compress_eq_comp (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (a : E →L[𝕜] E) :
    (isStarProjection_starProjection (U := U)).compress a =
      U.starProjection ∘L a ∘L U.starProjection := by
  simp only [IsStarProjection.compress, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc]

end Submodule
