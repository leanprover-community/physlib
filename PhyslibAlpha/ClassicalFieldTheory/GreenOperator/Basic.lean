/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Mathematics.Analysis.LocalOperator
public import PhyslibAlpha.Mathematics.Order.CausalRelation
public import Mathlib.Order.BourbakiWitt

/-!

# Green operators and causally supported fields

Retarded and advanced Green operators of a local operator.

## i. Overview

Retarded and advanced Green operators of a local operator. Fields with spacelike compact, future or
past compact support.

## ii. Key results

- `spacelikeCompactFields` : Admissible fields with support contained in the causal hull of a
  compact set.
- `futureSupportedFields` : Fields supported in the future of a compact set.
- `futureSupportedOperator` : Restrict the field equation to fields supported to the future of
  compact sets.
- `spacelikeCompactSolution` : Spacelike-compact homogeneous solutions.
- `spacelikeCompactOperator` : The field equation restricted to spacelike-compact admissible fields.
- `RetardedGreenOperator` : A retarded two-sided inverse on compact sources with future causal
  support.
- `AdvancedGreenOperator` : An advanced two-sided inverse on compact sources with past causal
  support.
- `GreenOperators` : A pair of causal Green inverses for the same field equation.

## iii. Table of contents

- A. Linear field equations and compact sources
- B. Retarded and advanced Green operators
- C. Past-compact and future-compact support

## iv. References

None.

## A. Linear field equations and compact sources

- `spacelikeCompactFields` : Admissible fields with support contained in the causal hull of a
  compact set.
- `futureSupportedFields` : Fields supported in the future of a compact set.
- `futureSupportedOperator` : Restrict the field equation to fields supported to the future of
  compact sets.
- `spacelikeCompactSolution` : Spacelike-compact homogeneous solutions.
- `spacelikeCompactOperator` : The field equation restricted to spacelike-compact admissible fields.

Lemmas: `operator_mem_futureSupportedFields`, `operator_mem_spacelikeCompactFields`,
`futureSupportedFields_le_spacelikeCompactFields`, `pastSupportedFields_le_spacelikeCompactFields`.

## B. Retarded and advanced Green operators

- `RetardedGreenOperator` : A retarded two-sided inverse on compact sources with future causal
  support.
- `AdvancedGreenOperator` : An advanced two-sided inverse on compact sources with past causal
  support.
- `GreenOperators` : A pair of causal Green inverses for the same field equation.
- `reverse` : Reverse time orientation and exchange the Green operators.

## C. Past-compact and future-compact support

- `pastCompactFields` : The full past-compact admissible source and field space.
- `pastCompactOperator` : The field equation restricted to the full past-compact support class.

Lemmas: `operator_mem_pastCompactFields`, `futureSupportedFields_le_pastCompactFields`.

-/

@[expose] public section

noncomputable section

open CausalRelation Submodule

namespace LocalOperator

section
variable {𝕜 M V : Type*} [Ring 𝕜] [TopologicalSpace M] [AddCommGroup V] [Module 𝕜 V]
variable {S : Submodule 𝕜 (M → V)} (P : LocalOperator S)

/-- Admissible fields with support contained in the causal hull of a compact set. -/
def spacelikeCompactFields (_P : LocalOperator S) (C : CausalRelation M) : Submodule 𝕜 S where
  carrier := {u | C.IsSpacelikeCompact (tsupport (u : M → V))}
  zero_mem' := by
    refine ⟨∅, isCompact_empty, ?_⟩
    simp
  add_mem' := by
    rintro u v ⟨K, hK, hu⟩ ⟨L, hL, hv⟩
    refine ⟨K ∪ L, hK.union hL, ?_⟩
    exact (tsupport_add (u : M → V) (v : M → V)).trans
      (Set.union_subset
        (hu.trans (C.causalHull_mono Set.subset_union_left))
        (hv.trans (C.causalHull_mono Set.subset_union_right)))
  smul_mem' := by
    intro a u hu
    exact IsSpacelikeCompact.mono C hu (tsupport_smul_subset_right (fun _ => a) (u :
      M → V))

/-- Fields supported in the future of a compact set. This is a strictly specified support class;
it is not identified with all past-compact fields without additional geometry. -/
def futureSupportedFields (_P : LocalOperator S) (C : CausalRelation M) : Submodule 𝕜 S where
  carrier := {u | ∃ K : Set M, IsCompact K ∧
    tsupport (u : M → V) ⊆ C.causalFuture K}
  zero_mem' := by
    refine ⟨∅, isCompact_empty, ?_⟩
    simp
  add_mem' := by
    rintro u v ⟨K, hK, hu⟩ ⟨L, hL, hv⟩
    refine ⟨K ∪ L, hK.union hL, ?_⟩
    exact (tsupport_add (u : M → V) (v : M → V)).trans
      (Set.union_subset
        (hu.trans (C.causalFuture_mono Set.subset_union_left))
        (hv.trans (C.causalFuture_mono Set.subset_union_right)))
  smul_mem' := by
    rintro a u ⟨K, hK, hu⟩
    exact ⟨K, hK, (tsupport_smul_subset_right (fun _ => a) (u : M → V)).trans hu⟩

/-- Locality preserves support in the causal future of a compact set. -/
lemma operator_mem_futureSupportedFields (C : CausalRelation M)
    {u : S} (hu : u ∈ P.futureSupportedFields C) :
    P.operator u ∈ P.futureSupportedFields C := by
  obtain ⟨K, hK, huK⟩ := hu
  exact ⟨K, hK, (P.support_operator u).trans huK⟩

/-- Restrict the field equation to fields supported to the future of compact sets. -/
def futureSupportedOperator (C : CausalRelation M) :
    P.futureSupportedFields C →ₗ[𝕜] P.futureSupportedFields C :=
  (P.operator.comp (P.futureSupportedFields C).subtype).codRestrict _
    (fun u => P.operator_mem_futureSupportedFields C u.property)

/-- Spacelike-compact homogeneous solutions. -/
def spacelikeCompactSolution (C : CausalRelation M) : Submodule 𝕜 S :=
  P.spacelikeCompactFields C ⊓ P.solutionSpace

/-- Locality preserves spacelike-compact support. -/
lemma operator_mem_spacelikeCompactFields (C : CausalRelation M)
    {u : S} (hu : u ∈ P.spacelikeCompactFields C) :
    P.operator u ∈ P.spacelikeCompactFields C :=
  IsSpacelikeCompact.mono C hu (P.support_operator u)

/-- One-sided compactly generated support is spacelike compact. -/
lemma futureSupportedFields_le_spacelikeCompactFields (C : CausalRelation M) :
    P.futureSupportedFields C ≤ P.spacelikeCompactFields C := by
  rintro u ⟨K, hK, hu⟩
  exact ⟨K, hK, hu.trans Set.subset_union_left⟩

/-- Past-supported compactly generated support is spacelike compact. -/
lemma pastSupportedFields_le_spacelikeCompactFields (C : CausalRelation M) :
    P.futureSupportedFields C.reverse ≤ P.spacelikeCompactFields C := by
  rintro u ⟨K, hK, hu⟩
  exact ⟨K, hK, hu.trans Set.subset_union_right⟩

/-- The field equation restricted to spacelike-compact admissible fields. -/
def spacelikeCompactOperator (C : CausalRelation M) :
    P.spacelikeCompactFields C →ₗ[𝕜] P.spacelikeCompactFields C :=
  (P.operator.comp (P.spacelikeCompactFields C).subtype).codRestrict _
    (fun u => P.operator_mem_spacelikeCompactFields C u.property)
end

end LocalOperator

namespace GreenOperator

open LocalOperator

section
variable {𝕜 M V : Type*} [Ring 𝕜] [TopologicalSpace M] [AddCommGroup V] [Module 𝕜 V] {S : Submodule
    𝕜 (M → V)}

/-- A retarded two-sided inverse on compact sources with future causal support. -/
structure RetardedGreenOperator (C : CausalRelation M) (P : LocalOperator S) where
  /-- Compact sources produce admissible fields without a compact support requirement. -/
  toLinearMap : P.compactSources →ₗ[𝕜] S
  /-- The response solves the prescribed sourced equation. -/
  solves : ∀ f, P.operator (toLinearMap f) = f.val
  /-- Compact fields are recovered from their equation of motion. -/
  comp_operator : ∀ f, toLinearMap (P.compactOperator f) = f.val
  /-- Retarded propagation is supported in the source's causal future. -/
  support : ∀ f, tsupport (toLinearMap f : M → V) ⊆
    C.causalFuture (tsupport (f.val : M → V))

/-- An advanced two-sided inverse on compact sources with past causal support. -/
structure AdvancedGreenOperator (C : CausalRelation M) (P : LocalOperator S) where
  /-- Compact sources produce unrestricted admissible fields. -/
  toLinearMap : P.compactSources →ₗ[𝕜] S
  /-- The response solves the prescribed sourced equation. -/
  solves : ∀ f, P.operator (toLinearMap f) = f.val
  /-- Compact fields are recovered from their equation of motion. -/
  comp_operator : ∀ f, toLinearMap (P.compactOperator f) = f.val
  /-- Advanced propagation is supported in the source's causal past. -/
  support : ∀ f, tsupport (toLinearMap f : M → V) ⊆
    C.causalPast (tsupport (f.val : M → V))

/-- A pair of causal Green inverses for the same field equation.
Formal-adjoint hypotheses and support extensions are not implicit in this bundle. -/
structure GreenOperators (C : CausalRelation M) (P : LocalOperator S) where
  /-- The retarded Green inverse. -/
  retarded : RetardedGreenOperator C P
  /-- The advanced Green inverse. -/
  advanced : AdvancedGreenOperator C P
end

end GreenOperator

namespace GreenOperator.GreenOperators

open LocalOperator

section
variable {𝕜 M V : Type*} [Ring 𝕜] [TopologicalSpace M] [AddCommGroup V] [Module 𝕜 V] {S : Submodule
    𝕜 (M → V)}
variable {C : CausalRelation M} {P : LocalOperator S} (G : GreenOperators C P)

/-- Reverse time orientation and exchange the Green operators. -/
def reverse : GreenOperators C.reverse P where
  retarded := ⟨G.advanced.toLinearMap, G.advanced.solves,
    G.advanced.comp_operator, G.advanced.support⟩
  advanced := ⟨G.retarded.toLinearMap, G.retarded.solves,
    G.retarded.comp_operator, G.retarded.support⟩
end

end GreenOperator.GreenOperators

namespace LocalOperator

section
variable {𝕜 M V : Type*} [Ring 𝕜] [TopologicalSpace M] [AddCommGroup V] [Module 𝕜 V] {S : Submodule
    𝕜 (M → V)} (P : LocalOperator S) (C : CausalRelation M)

/-- The full past-compact admissible source and field space. -/
def pastCompactFields (_P : LocalOperator S) (C : CausalRelation M) : Submodule 𝕜 S where
  carrier := {u | C.IsPastCompact (tsupport (u : M → V))}
  zero_mem' := by simpa using C.isPastCompact_empty
  add_mem' := by
    intro u v hu hv
    exact IsPastCompact.mono C
      (IsPastCompact.union C hu hv) (isClosed_tsupport _)
      (tsupport_add (u : M → V) (v : M → V))
  smul_mem' := by
    intro a u hu
    exact IsPastCompact.mono C hu (isClosed_tsupport _)
      (tsupport_smul_subset_right (fun _ => a) (u : M → V))

/-- Local field equations preserve past-compact support. -/
lemma operator_mem_pastCompactFields {u : S} (hu : u ∈ P.pastCompactFields C) :
    P.operator u ∈ P.pastCompactFields C :=
  IsPastCompact.mono C hu (isClosed_tsupport _) (P.support_operator u)

/-- The field equation restricted to the full past-compact support class. -/
def pastCompactOperator : P.pastCompactFields C →ₗ[𝕜] P.pastCompactFields C :=
  (P.operator.comp (P.pastCompactFields C).subtype).codRestrict _
    (fun u => P.operator_mem_pastCompactFields C u.property)

/-- Support in the future of one compact set is included in the full past-compact class. -/
lemma futureSupportedFields_le_pastCompactFields (hC : C.HasCompactCausalDiamonds) :
    P.futureSupportedFields C ≤ P.pastCompactFields C := by
  rintro u ⟨K, hK, huK⟩
  exact C.isPastCompact_of_futureSupported hC (isClosed_tsupport _) hK huK
end

end LocalOperator
