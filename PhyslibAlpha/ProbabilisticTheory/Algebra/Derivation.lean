/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Abel

/-!

# Derivations

Derivations of a bilinear multiplication and their closure under linear operations.

## i. Overview

A derivation of a multiplication is a linear map `D` with `D (a b) = D a b + a D b`. The notion only
needs a bilinear product, so it covers associative and Jordan derivations alike. Derivations form a
real vector space.

## ii. Key results

- `IsDerivation` : derivations.
- `IsDerivation.add`, `IsDerivation.smul` : derivations form a vector space.

## iii. Table of contents

- A. The Leibniz rule
- B. Closure properties

## iv. References

* None.

-/

@[expose] public section

namespace ProbabilisticTheory

/-! ## A. The Leibniz rule -/

/-- `D` is a derivation of the multiplication on `E`: `D (a b) = D a b + a D b`. Only a
multiplication and a real module structure are assumed, so that it applies to normed spaces with a
separate product. -/
def IsDerivation {E : Type*} [Mul E] [AddCommGroup E] [Module ℝ E] (D : E →ₗ[ℝ] E) :
    Prop :=
  ∀ a b : E, D (a * b) = D a * b + a * D b

/-! ## B. Closure properties -/

variable {E : Type*} [NonUnitalNonAssocRing E] [Module ℝ E]

lemma IsDerivation.zero : IsDerivation (0 : E →ₗ[ℝ] E) := by
  intro a b; simp

lemma IsDerivation.add {D₁ D₂ : E →ₗ[ℝ] E} (h₁ : IsDerivation D₁) (h₂ : IsDerivation D₂) :
    IsDerivation (D₁ + D₂) := by
  intro a b
  simp only [LinearMap.add_apply, h₁ a b, h₂ a b, add_mul, mul_add]
  abel

lemma IsDerivation.neg {D : E →ₗ[ℝ] E} (h : IsDerivation D) : IsDerivation (-D) := by
  intro a b
  simp only [LinearMap.neg_apply, h a b, neg_mul, mul_neg, neg_add_rev]
  abel

lemma IsDerivation.smul [SMulCommClass ℝ E E] [IsScalarTower ℝ E E] (c : ℝ) {D : E →ₗ[ℝ] E}
    (h : IsDerivation D) : IsDerivation (c • D) := by
  intro a b
  simp only [LinearMap.smul_apply, h a b, smul_add, smul_mul_assoc, mul_smul_comm]

end ProbabilisticTheory
