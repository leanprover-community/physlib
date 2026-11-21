/-
Copyright (c) 2026 Chengyuan AI Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qianli Ma
-/
module

public import Mathlib.Algebra.Star.StarProjection

/-!
# Compression by a projection

## i. Overview

The compression of `a` by `p` is the product `p * a * p`. If `p` is idempotent, then
compression by `p` is an idempotent map. If `p` is self-adjoint, compression commutes
with the star operation. A star projection has both properties.

## ii. Key results

- `Projection.compress` defines compression using only multiplication.
- `IsIdempotentElem.compress_comp_compress` gives idempotence of the compression map.
- `IsSelfAdjoint.star_compress` relates compression and the star operation.

## iii. Table of contents

- A. Compression
- B. Compression by an idempotent
- C. Compression by a self-adjoint element

## iv. References

* None.
-/

@[expose] public section

/-!
## A. Compression
-/

namespace Projection

variable {A : Type*}

/-- The compression of `a` by an idempotent element `p`, given by `p * a * p`. -/
def compress [Mul A] (p a : A) : A := p * a * p

lemma compress_apply [Mul A] (p a : A) : compress p a = p * a * p := rfl

@[simp] lemma compress_zero [MulZeroClass A] (p : A) : compress p 0 = 0 := by
  simp only [compress_apply, mul_zero, zero_mul]

@[simp] lemma zero_compress_apply [MulZeroClass A] (a : A) : compress 0 a = 0 := by
  simp only [compress_apply, zero_mul]

@[simp] lemma zero_compress [MulZeroClass A] : compress (0 : A) = 0 :=
  funext zero_compress_apply

lemma compress_add [Distrib A] (p a b : A) :
    compress p (a + b) = compress p a + compress p b := by
  simp only [compress_apply, mul_add, add_mul]

end Projection

open Projection

/-!
## B. Compression by an idempotent
-/

namespace IsIdempotentElem

variable {A : Type*} [Semigroup A] {p : A} (hp : IsIdempotentElem p)

include hp

/-- Multiplying a compression by its idempotent on the left leaves it unchanged. -/
@[simp] lemma mul_compress (a : A) : p * compress p a = compress p a := by
  simp only [compress_apply, ← mul_assoc, hp.eq]

/-- Multiplying a compression by its idempotent on the right leaves it unchanged. -/
@[simp] lemma compress_mul (a : A) : compress p a * p = compress p a := by
  simp only [compress_apply, mul_assoc, hp.eq]

/-- Compression by the same idempotent twice gives the original compression. -/
@[simp] lemma compress_compress (a : A) : compress p (compress p a) = compress p a := by
  rw [compress_apply, hp.mul_compress, hp.compress_mul]

/-- Compression by an idempotent is idempotent under function composition. -/
@[simp] lemma compress_comp_compress : compress p ∘ compress p = compress p :=
  funext hp.compress_compress

/-- The product of two compressions is a compression with an intermediate idempotent. -/
lemma compress_mul_compress (a b : A) : compress p a * compress p b = compress p (a * p * b) := by
  simp only [compress_apply, mul_assoc, hp.mul_self_mul]

end IsIdempotentElem

/-!
## C. Compression by a self-adjoint element
-/

namespace IsSelfAdjoint

variable {A : Type*} [Semigroup A] [StarMul A] {p : A} (hp : IsSelfAdjoint p)

include hp

/-- Compression by a self-adjoint element commutes with taking the star. -/
lemma star_compress (a : A) : star (compress p a) = compress p (star a) := by
  simp only [compress_apply, star_mul, hp.star_eq, mul_assoc]

/-- Compression by a self-adjoint element preserves self-adjointness. -/
lemma isSelfAdjoint_compress {a : A} (ha : IsSelfAdjoint a) : IsSelfAdjoint (compress p a) :=
  ha.conjugate_self hp

end IsSelfAdjoint
