/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.LinearAlgebra.Complex.Module
public import PhyslibAlpha.ProbabilisticTheory.State.Basic

/-!

# Expectation values of non-self-adjoint operators

A state is defined on the self-adjoint observables, and extends uniquely to a complex-linear
functional on all operators.

## i. Overview

A state assigns an expectation value to every observable, a self-adjoint operator. Correlation
functions such as `⟨A B(t)⟩` involve products of observables, which are not self-adjoint, and so
need the expectation value of an arbitrary operator `a`. Every operator is uniquely a combination
`a = ℜ a + i ℑ a` of two self-adjoint operators, its real and imaginary parts, and the expectation
value is extended by linearity: `⟨a⟩ = ⟨ℜ a⟩ + i ⟨ℑ a⟩`. This is the unique complex-linear extension
of the state that is compatible with taking adjoints, `⟨a*⟩ = conj ⟨a⟩`.

## ii. Key results

- `complexExtension` : the complex-linear functional extending an expectation value.
- `complexExtension_coe` : on self-adjoint operators it is the original expectation value.
- `complexExtension_star` : the expectation value of the adjoint is the complex conjugate.

## iii. Table of contents

- A. The extension
- B. Properties
- C. Compatibility with `*`-linear maps

## iv. References

* O. Bratteli & D. Robinson, Operator Algebras and Quantum Statistical Mechanics 1, 2nd ed.,
  Chapter 2.
-/

@[expose] public section

namespace ProbabilisticTheory

open ComplexStarModule

variable {A : Type*} [AddCommGroup A] [Module ℂ A] [StarAddMonoid A] [StarModule ℂ A]

/-!

## A. The extension

-/

/-- The complex-linear extension of an expectation value on self-adjoint operators to all
operators: `⟨a⟩ = ⟨ℜ a⟩ + i ⟨ℑ a⟩`. -/
noncomputable def complexExtension (φ : selfAdjoint A →ₗ[ℝ] ℝ) : A →ₗ[ℂ] ℂ where
  toFun a := φ (ℜ a) + Complex.I * φ (ℑ a)
  map_add' a b := by
    simp only [map_add, Complex.ofReal_add]
    ring
  map_smul' z a := by
    simp only [realPart_smul, imaginaryPart_smul, map_add, map_sub, map_smul, smul_eq_mul,
      RingHom.id_apply, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_sub]
    apply Complex.ext <;> simp

lemma complexExtension_apply (φ : selfAdjoint A →ₗ[ℝ] ℝ) (a : A) :
    complexExtension φ a = φ (ℜ a) + Complex.I * φ (ℑ a) := rfl

/-!

## B. Properties

-/

/-- On self-adjoint operators the extension is the original expectation value. -/
lemma complexExtension_coe (φ : selfAdjoint A →ₗ[ℝ] ℝ) (a : selfAdjoint A) :
    complexExtension φ (a : A) = φ a := by
  simp [complexExtension_apply]

/-- The expectation value of the adjoint is the complex conjugate of the expectation value. -/
lemma complexExtension_star (φ : selfAdjoint A →ₗ[ℝ] ℝ) (a : A) :
    complexExtension φ (star a) = starRingEnd ℂ (complexExtension φ a) := by
  have hr : ℜ (star a) = ℜ a := by
    ext; simp [realPart_apply_coe, add_comm]
  have hi : ℑ (star a) = -ℑ a := by
    ext
    simp [imaginaryPart_apply_coe, sub_eq_add_neg, add_comm, smul_neg]
  simp [complexExtension_apply, hr, hi]

/-!

## C. Compatibility with `*`-linear maps

-/

section Hom

variable {C D : Type*} [AddCommGroup C] [Module ℂ C] [StarAddMonoid C] [StarModule ℂ C]
  [AddCommGroup D] [Module ℂ D] [StarAddMonoid D] [StarModule ℂ D]

/-- A complex-linear map commuting with the adjoint maps the real part of an operator to the real
part of its image. -/
lemma realPart_linearMap (f : C →ₗ[ℂ] D) (hf : ∀ a, f (star a) = star (f a)) (a : C) :
    ((ℜ (f a) : selfAdjoint D) : D) = f (ℜ a : C) := by
  rw [realPart_apply_coe, realPart_apply_coe]
  simp only [← Complex.coe_smul, map_smul, map_add, hf]

/-- A complex-linear map commuting with the adjoint maps the imaginary part of an operator to the
imaginary part of its image. -/
lemma imaginaryPart_linearMap (f : C →ₗ[ℂ] D) (hf : ∀ a, f (star a) = star (f a)) (a : C) :
    ((ℑ (f a) : selfAdjoint D) : D) = f (ℑ a : C) := by
  rw [imaginaryPart_apply_coe, imaginaryPart_apply_coe]
  simp only [← Complex.coe_smul, map_smul, map_sub, hf]

end Hom

end ProbabilisticTheory
