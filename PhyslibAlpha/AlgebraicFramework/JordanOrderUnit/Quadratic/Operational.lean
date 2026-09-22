/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.JordanOrderUnit.Quadratic.Order
public import PhyslibAlpha.AlgebraicFramework.JordanOrderUnit.Quadratic.Fundamental

/-!
# Sequential quadratic operations

This module is the meeting point of ordered quadratic operations and the purely algebraic
fundamental formula.  `Quadratic/Order.lean` deliberately remains independent of the latter:
positivity itself needs only the linear quadratic representation.  Once both facts are available,
the fundamental formula becomes an equality of bundled positive operations, suitable for
measurement and JBW clients.
-/

@[expose] public section

namespace JordanAlgebra

open scoped JordanAlgebra

variable {E : Type*} [NonAssocCommRing E] [PartialOrder E] [IsOrderedAddMonoid E]
  [Module ℝ E] [SMulCommClass ℝ E E] [IsQuadraticallyPositive E] [IsCommJordan E]

/-- Squaring the filtering observable composes its positive quadratic operation with itself.
This is the bundled operational form of `U_(a²) = U_a ∘ U_a`. -/
theorem quadRepPositiveLinearMap_mul_self (a : E) :
    quadRepPositiveLinearMap (a * a) =
      (quadRepPositiveLinearMap a).comp (quadRepPositiveLinearMap a) := by
  apply PositiveLinearMap.ext
  intro x
  change U (a * a) x = U a (U a x)
  exact DFunLike.congr_fun (quadRep_mul_self_eq_comp a) x

/-- The quadratic fundamental formula as an equality of positive operations.  Thus a filter
whose observable is `U_a b` is precisely the sequential filter `U_a`, then `U_b`, then `U_a`.
The statement is intrinsic Jordan algebra; positivity is used only to bundle the maps. -/
theorem quadRepPositiveLinearMap_fundamental (a b : E) :
    quadRepPositiveLinearMap (U a b) =
      (quadRepPositiveLinearMap a).comp
        ((quadRepPositiveLinearMap b).comp (quadRepPositiveLinearMap a)) := by
  apply PositiveLinearMap.ext
  intro x
  change U (U a b) x = U a (U b (U a x))
  exact quadRep_fundamental_apply a b x

end JordanAlgebra
