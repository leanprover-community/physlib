/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import PhyslibAlpha.Mathematics.RepresentationTheory.Sl2.BivariateBasis

/-!
# Classification for two commuting sl₂ actions

Uses the bivariate basis to obtain a tensor-product vector-space description.

## i. Overview

For two commuting `sl₂` triples acting jointly irreducibly, the bivariate ladder basis
gives a linear equivalence with a tensor product of standard modules and a corresponding
dimension formula. The equivalence is only one of vector spaces; it does not assert that the
actions intertwine.

## ii. Key results

- `commuting_classification` gives the vector-space equivalence.
- `commuting_classification_finrank` gives the dimension formula.

## iii. Table of contents

- A. Two commuting actions

## iv. References

- Mathlib, `Mathlib.Algebra.Lie.Sl2`.

## A. Two commuting actions
-/

@[expose] public section

noncomputable section

namespace PhyslibAlpha.Sl2

open scoped TensorProduct

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The standard module `V(k)` has dimension `k + 1`. -/
lemma finrank_standardSl2Module (k : ℕ) : Module.finrank K (StandardSl2Module K k) = k + 1 := by
  show Module.finrank K (Fin (k + 1) → K) = k + 1
  rw [Module.finrank_pi, Fintype.card_fin]

section Joint

variable [IsAlgClosed K] [CharZero K] [FiniteDimensional K V]
    {h1 e1 f1 h2 e2 f2 : Module.End K V}
    (t1 : IsSl2Triple h1 e1 f1) (t2 : IsSl2Triple h2 e2 f2)
    (hcomm : ∀ x ∈ ({h1, e1, f1} : Set (Module.End K V)),
      ∀ y ∈ ({h2, e2, f2} : Set (Module.End K V)), ⁅x, y⁆ = 0)
    (hirr : JointlyIrreducible h1 e1 f1 h2 e2 f2)

include t1 t2 hcomm hirr

/-- Dimension consequence of `commuting_classification`: `finrank K V = (m+1)(n+1)`. -/
lemma commuting_classification_finrank :
    ∃ m n : ℕ, Module.finrank K V = (m + 1) * (n + 1) := by
  obtain ⟨n1, n2, B, -⟩ := exists_bivariate_basis t1 t2 hcomm hirr
  exact ⟨n1, n2, by
    rw [Module.finrank_eq_card_basis B, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]⟩


/-- Classification of jointly irreducible commuting `sl₂`-actions.
Two `sl₂`-triples of operators on a
finite-dimensional space `V`, commuting with each other and with no proper
subspace invariant under both, force `V` to be linearly isomorphic to a tensor
product `V(m) ⊗ V(n)` of standard modules.

The equivalence is obtained from a dimension count. An equivalence intertwining the two
actions remains to be constructed. -/
lemma commuting_classification :
    ∃ m n : ℕ, Nonempty (V ≃ₗ[K] StandardSl2Module K m ⊗[K] StandardSl2Module K n) := by
  obtain ⟨n1, n2, hdim⟩ := commuting_classification_finrank t1 t2 hcomm hirr
  refine ⟨n1, n2, FiniteDimensional.nonempty_linearEquiv_of_finrank_eq ?_⟩
  rw [hdim, Module.finrank_tensorProduct, finrank_standardSl2Module, finrank_standardSl2Module]

end Joint

end PhyslibAlpha.Sl2
