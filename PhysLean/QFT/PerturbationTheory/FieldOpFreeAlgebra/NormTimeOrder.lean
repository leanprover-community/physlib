/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhysLean.QFT.PerturbationTheory.FieldSpecification.TimeOrder
public import PhysLean.QFT.PerturbationTheory.FieldOpFreeAlgebra.Basic
/-!

# Norm-time Ordering in the FieldOpFreeAlgebra

-/

@[expose] public section

namespace FieldSpecification
variable {𝓕 : FieldSpecification}
open FieldStatistic

namespace FieldOpFreeAlgebra

noncomputable section
open Module PhysLean.List

/-!

## Norm-time order

-/

/-- The normal-time ordering on `FieldOpFreeAlgebra`. -/
def normTimeOrder : FieldOpFreeAlgebra 𝓕 →ₗ[ℂ] FieldOpFreeAlgebra 𝓕 :=
  Basis.constr ofCrAnListFBasis ℂ fun φs =>
  normTimeOrderSign φs • ofCrAnListF (normTimeOrderList φs)

@[inherit_doc normTimeOrder]
scoped[FieldSpecification.FieldOpFreeAlgebra] notation "𝓣𝓝ᶠ(" a ")" => normTimeOrder a

lemma normTimeOrder_ofCrAnListF (φs : List 𝓕.CrAnFieldOp) :
    𝓣𝓝ᶠ(ofCrAnListF φs) = normTimeOrderSign φs • ofCrAnListF (normTimeOrderList φs) := by
  rw [← ofListBasis_eq_ofList]
  simp only [normTimeOrder, Basis.constr_basis]

end

end FieldOpFreeAlgebra

end FieldSpecification
