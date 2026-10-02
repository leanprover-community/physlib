/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.JordanOrderUnit.Operator
public import Mathlib.Algebra.Order.Module.PositiveLinearMap

/-!

# Positive quadratic representations

## i. Overview

The quadratic representation `U_a` is the Jordan version of the operation `b ↦ a b a`. A Jordan
order-unit space is quadratically positive when every `U_a` preserves the positive cone; then each
`U_a` is a positive linear map.

## ii. Key results

- `JordanAlgebra.IsQuadraticallyPositive` : quadratically positive Jordan order-unit spaces.
- `JordanAlgebra.quadRepPositiveLinearMap` : `U_a` as a positive linear map.

-/

@[expose] public section

namespace ProbabilisticTheory

namespace JordanAlgebra

open scoped JordanAlgebra

variable {E : Type*} [NonAssocCommRing E] [PartialOrder E] [IsOrderedAddMonoid E]
  [Module ℝ E] [SMulCommClass ℝ E E]

/-- Every quadratic representation `U_a` preserves the positive cone. -/
class IsQuadraticallyPositive (E : Type*) [NonAssocCommRing E] [PartialOrder E]
    [IsOrderedAddMonoid E] [Module ℝ E] [SMulCommClass ℝ E E] : Prop where
  quadRep_nonneg : ∀ (a : E) {b : E}, 0 ≤ b → 0 ≤ U a b

variable [IsQuadraticallyPositive E]

/-- Quadratic representations map nonnegative observables to nonnegative observables. -/
lemma quadRep_nonneg (a : E) {b : E} (hb : 0 ≤ b) : 0 ≤ U a b :=
  IsQuadraticallyPositive.quadRep_nonneg a hb

/-- The quadratic representation as a bundled positive linear operation. -/
def quadRepPositiveLinearMap (a : E) : E →ₚ[ℝ] E :=
  PositiveLinearMap.mk₀ (U a) fun _ hb => quadRep_nonneg a hb

@[simp]
lemma coe_quadRepPositiveLinearMap (a : E) :
    (quadRepPositiveLinearMap a : E →ₗ[ℝ] E) = U a :=
  rfl

@[simp]
lemma quadRepPositiveLinearMap_apply (a b : E) : quadRepPositiveLinearMap a b = U a b :=
  rfl

/-- The unit has the identity quadratic operation. -/
@[simp]
lemma quadRepPositiveLinearMap_one :
    quadRepPositiveLinearMap (1 : E) = PositiveLinearMap.id ℝ E := by
  apply PositiveLinearMap.ext
  intro x
  exact quadRep_one_apply x

/-- Positivity of `U a` implies monotonicity. -/
lemma quadRep_monotone (a : E) : Monotone (U a) := by
  intro b c hbc
  rw [← sub_nonneg] at hbc ⊢
  rw [← map_sub]
  exact quadRep_nonneg a hbc

end JordanAlgebra

end ProbabilisticTheory
