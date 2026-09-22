/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.JordanOrderUnit.Operator
public import Mathlib.Algebra.Order.Module.PositiveLinearMap

/-!

# Positive quadratic representations

The quadratic representation `U a` is the intrinsic Jordan version of the
self-adjoint one-Kraus operation `b ↦ aba`.  Its preservation of the positive cone is the
precise operational fact used by compression and conditioning.  It is intentionally a separate
capability: square positivity alone does not prove it for an arbitrary supplied cone, and the
intrinsic JB theorem which discharges this capability belongs to the later spectral development.

Concrete realizations and, eventually, genuine JB theory provide this class.  Physics-facing
results should require it directly rather than importing a proof through a special associative
realization.

-/

@[expose] public section

namespace JordanAlgebra

open scoped JordanAlgebra

variable {E : Type*} [NonAssocCommRing E] [PartialOrder E] [IsOrderedAddMonoid E]
  [Module ℝ E] [SMulCommClass ℝ E E]

/-- Quadratic representations preserve the given positive cone.  This is an operational ordered
Jordan capability, not a consequence claimed from the weak square-positive order-unit interface.
The intended intrinsic provider is the JB quadratic-positivity theorem; special realizations can
also provide it directly from `U_a(b) = aba`. -/
class IsQuadraticallyPositive (E : Type*) [NonAssocCommRing E] [PartialOrder E]
    [IsOrderedAddMonoid E] [Module ℝ E] [SMulCommClass ℝ E E] : Prop where
  quadRep_nonneg : ∀ (a : E) {b : E}, 0 ≤ b → 0 ≤ U a b

variable [IsQuadraticallyPositive E]

/-- Quadratic representations map nonnegative observables to nonnegative observables. -/
theorem quadRep_nonneg (a : E) {b : E} (hb : 0 ≤ b) : 0 ≤ U a b :=
  IsQuadraticallyPositive.quadRep_nonneg a hb

/-- The quadratic representation as a bundled positive linear operation. -/
def quadRepPositiveLinearMap (a : E) : E →ₚ[ℝ] E :=
  PositiveLinearMap.mk₀ (U a) fun _ hb => quadRep_nonneg a hb

@[simp]
theorem coe_quadRepPositiveLinearMap (a : E) :
    (quadRepPositiveLinearMap a : E →ₗ[ℝ] E) = U a :=
  rfl

@[simp]
theorem quadRepPositiveLinearMap_apply (a b : E) : quadRepPositiveLinearMap a b = U a b :=
  rfl

/-- The unit has the identity quadratic operation. -/
@[simp]
theorem quadRepPositiveLinearMap_one :
    quadRepPositiveLinearMap (1 : E) = PositiveLinearMap.id ℝ E := by
  apply PositiveLinearMap.ext
  intro x
  exact quadRep_one_apply x

/-- Positivity of `U a` implies monotonicity. -/
theorem quadRep_monotone (a : E) : Monotone (U a) := by
  intro b c hbc
  rw [← sub_nonneg] at hbc ⊢
  rw [← map_sub]
  exact quadRep_nonneg a hbc

end JordanAlgebra
