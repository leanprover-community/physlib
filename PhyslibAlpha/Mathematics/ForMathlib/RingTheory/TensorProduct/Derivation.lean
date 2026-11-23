/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import Mathlib.RingTheory.TensorProduct.Basic
/-!
# Derivations of one factor of a tensor product of algebras

A derivation of one factor of a tensor product of algebras extends to the tensor product.

## i. Overview

A linear map `D` of an algebra `A` satisfying the Leibniz rule
`D (x * y) = D x * y + x * D y` extends to the tensor product `A ⊗[R] B` as `D ⊗ id`, and the
extension satisfies the Leibniz rule again. On pure tensors this is the Leibniz rule of `D`
in the first factor, the second factor being carried along, and the general case follows by
additivity. The same holds for a derivation of the right factor, extended as `id ⊗ D`.

## ii. Key results

- `TensorProduct.map_derivation_left` : a derivation of the left factor extends to a
  derivation of the tensor product.
- `TensorProduct.map_derivation_right` : a derivation of the right factor extends to a
  derivation of the tensor product.

## iii. Table of contents

- A. Derivations of one factor

## iv. References

* None.

-/

@[expose] public section

namespace TensorProduct

/-!

## A. Derivations of one factor

-/

/-- A derivation of the left factor extends to a derivation of the tensor product. -/
lemma map_derivation_left {R A B : Type*} [CommRing R] [Ring A] [Algebra R A]
    [Ring B] [Algebra R B] (D : A →ₗ[R] A)
    (hD : ∀ x y, D (x * y) = D x * y + x * D y) (x y : A ⊗[R] B) :
    TensorProduct.map D LinearMap.id (x * y)
      = TensorProduct.map D LinearMap.id x * y
        + x * TensorProduct.map D LinearMap.id y := by
  induction x using TensorProduct.inductionOn with
  | add x₁ x₂ h₁ h₂ =>
    rw [add_mul, map_add, map_add, h₁, h₂, add_mul, add_mul]
    abel
  | tmul a₁ b₁ =>
    induction y using TensorProduct.inductionOn with
    | add y₁ y₂ h₁ h₂ =>
      rw [mul_add, map_add, map_add, h₁, h₂, mul_add, mul_add]
      abel
    | tmul a₂ b₂ =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.map_tmul,
        TensorProduct.map_tmul, TensorProduct.map_tmul, LinearMap.id_apply,
        LinearMap.id_apply, LinearMap.id_apply, hD, TensorProduct.add_tmul,
        Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul]

/-- A derivation of the right factor extends to a derivation of the tensor product. -/
lemma map_derivation_right {R A B : Type*} [CommRing R] [Ring A] [Algebra R A]
    [Ring B] [Algebra R B] (D : B →ₗ[R] B)
    (hD : ∀ x y, D (x * y) = D x * y + x * D y) (x y : A ⊗[R] B) :
    TensorProduct.map LinearMap.id D (x * y)
      = TensorProduct.map LinearMap.id D x * y
        + x * TensorProduct.map LinearMap.id D y := by
  induction x using TensorProduct.inductionOn with
  | add x₁ x₂ h₁ h₂ =>
    rw [add_mul, map_add, map_add, h₁, h₂, add_mul, add_mul]
    abel
  | tmul a₁ b₁ =>
    induction y using TensorProduct.inductionOn with
    | add y₁ y₂ h₁ h₂ =>
      rw [mul_add, map_add, map_add, h₁, h₂, mul_add, mul_add]
      abel
    | tmul a₂ b₂ =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.map_tmul,
        TensorProduct.map_tmul, TensorProduct.map_tmul, LinearMap.id_apply,
        LinearMap.id_apply, LinearMap.id_apply, hD, TensorProduct.tmul_add,
        Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul]

end TensorProduct
