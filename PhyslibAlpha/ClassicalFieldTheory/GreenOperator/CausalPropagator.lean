/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.GreenOperator.Basic
public import Mathlib.Algebra.Module.Submodule.Range

/-!

# The causal propagator and causal uniqueness

The difference of the retarded and advanced response solves the homogeneous equation.

## i. Overview

The difference of the retarded and advanced response solves the homogeneous equation. Uniqueness of
one-sided solutions follows from the support of the response.

## ii. Key results

- `causalPropagator` : The causal propagator uses the sign convention retarded minus advanced.
- `toSolutionSpace` : The causal propagator with its proven solution-space codomain.
- `HasCausalCutoffs` : Temporal cutoff splitting of spacelike-compact admissible fields.
- `eq_of_local_truncations` : Compact truncations agreeing with the same field in the observation's
  causal past give identical retarded responses.

## iii. Table of contents

- A. The causal propagator and compact source kernel
- B. Causal splitting and one-sided uniqueness
- C. Local field equations and causal agreement

## iv. References

None.

## A. The causal propagator and compact source kernel

- `causalPropagator` : The causal propagator uses the sign convention retarded minus advanced.
- `toSolutionSpace` : The causal propagator with its proven solution-space codomain.

Lemmas: `causalPropagator_solves`, `causalPropagator_comp_operator`, `causalPropagator_support`,
`causalPropagator_mem_solution`, `range_compactOperator_le_ker`, `compactOperator_injective`,
`retarded_compact_of_causalPropagator_eq_zero`, `mem_range_of_causalPropagator_eq_zero`,
`causalPropagator_ker`, `toSolutionSpace_ker`.

## B. Causal splitting and one-sided uniqueness

- `HasCausalCutoffs` : Temporal cutoff splitting of spacelike-compact admissible fields.

Lemmas: `futureSupported_unique`, `retarded_mem_futureSupportedFields`,
`advanced_mem_futureSupportedFields_reverse`, `retarded_eq_of_futureSupported`,
`advanced_eq_of_pastSupported`.

## C. Local field equations and causal agreement

Lemmas: `eq_zero_of_no_causal_source`, `eq_of_no_causal_difference`, `eq_of_local_truncations`.

-/

@[expose] public section

noncomputable section

open scoped Topology
open CausalRelation Submodule

namespace GreenOperator.GreenOperators

open LocalOperator

section
variable {𝕜 M V : Type*} [Ring 𝕜] [TopologicalSpace M] [AddCommGroup V] [Module 𝕜 V] {S : Submodule
    𝕜 (M → V)} {C : CausalRelation M} {P : LocalOperator S} (G : GreenOperators C P)

/-- Fix the inherited field addition for nested quotient inference. -/
local instance greenFieldAddGroup : AddCommGroup S := S.addCommGroup

/-- The causal propagator uses the sign convention retarded minus advanced. -/
def causalPropagator : P.compactSources →ₗ[𝕜] S :=
  G.retarded.toLinearMap - G.advanced.toLinearMap

/-- The causal propagator produces homogeneous fields. -/
lemma causalPropagator_solves (f : P.compactSources) :
    P.operator (G.causalPropagator f) = 0 := by
  change P.operator (G.retarded.toLinearMap f - G.advanced.toLinearMap f) = 0
  rw [map_sub, G.retarded.solves, G.advanced.solves, sub_self]

/-- Test sources differing by the field equation give the same causal response. -/
lemma causalPropagator_comp_operator (f : P.compactSources) :
    G.causalPropagator (P.compactOperator f) = 0 := by
  change G.retarded.toLinearMap (P.compactOperator f) -
    G.advanced.toLinearMap (P.compactOperator f) = 0
  rw [G.retarded.comp_operator, G.advanced.comp_operator, sub_self]

/-- Causal propagation is supported in the union of the future and past of its source. -/
lemma causalPropagator_support (f : P.compactSources) :
    tsupport (G.causalPropagator f : M → V) ⊆ C.causalHull (tsupport (f.val : M → V)) :=
  (tsupport_sub (G.retarded.toLinearMap f : M → V)
    (G.advanced.toLinearMap f : M → V)).trans
    (Set.union_subset_union (G.retarded.support f) (G.advanced.support f))

/-- Compact source support yields spacelike-compact homogeneous response. -/
lemma causalPropagator_mem_solution (f : P.compactSources) :
    G.causalPropagator f ∈ P.spacelikeCompactSolution C :=
  ⟨⟨tsupport (f.val : M → V), f.property, G.causalPropagator_support f⟩,
    G.causalPropagator_solves f⟩

/-- The causal propagator with its proven solution-space codomain. -/
def toSolutionSpace : P.compactSources →ₗ[𝕜] P.spacelikeCompactSolution C :=
  G.causalPropagator.codRestrict _ G.causalPropagator_mem_solution

/-- Equations of motion are in the kernel of the causal propagator.
The reverse inclusion requires causal compactness and additional arguments. -/
lemma range_compactOperator_le_ker :
    LinearMap.range P.compactOperator ≤ LinearMap.ker G.causalPropagator := by
  rintro _ ⟨f, rfl⟩
  exact G.causalPropagator_comp_operator f

include G in
/-- A compact homogeneous field vanishes because either Green operator is a left inverse. -/
lemma compactOperator_injective : Function.Injective P.compactOperator := by
  intro f g h
  apply Subtype.ext
  have heq := congrArg G.retarded.toLinearMap h
  simpa only [G.retarded.comp_operator] using heq

/-- A source in the causal-propagator kernel has a compact retarded response. -/
lemma retarded_compact_of_causalPropagator_eq_zero (hC : C.HasCompactCausalDiamonds)
    (f : P.compactSources) (hf : G.causalPropagator f = 0) :
    HasCompactSupport (G.retarded.toLinearMap f : M → V) := by
  have heq : G.retarded.toLinearMap f = G.advanced.toLinearMap f := sub_eq_zero.mp hf
  apply (hC _ _ f.property f.property).of_isClosed_subset (isClosed_tsupport _)
  exact Set.subset_inter (G.retarded.support f) (heq ▸ G.advanced.support f)

/-- Every zero causal response is an equation-of-motion source of a compact field. -/
lemma mem_range_of_causalPropagator_eq_zero (hC : C.HasCompactCausalDiamonds)
    (f : P.compactSources) (hf : G.causalPropagator f = 0) :
    f ∈ LinearMap.range P.compactOperator := by
  let u : P.compactSources :=
    ⟨G.retarded.toLinearMap f, G.retarded_compact_of_causalPropagator_eq_zero hC f hf⟩
  refine ⟨u, ?_⟩
  apply Subtype.ext
  exact G.retarded.solves f

/-- The kernel of the causal propagator consists precisely of equation-of-motion sources.
The proof uses compact causal diamonds rather than an assumed exactness hypothesis. -/
lemma causalPropagator_ker (hC : C.HasCompactCausalDiamonds) :
    LinearMap.ker G.causalPropagator = LinearMap.range P.compactOperator := by
  apply le_antisymm
  · intro f hf
    exact G.mem_range_of_causalPropagator_eq_zero hC f hf
  · exact G.range_compactOperator_le_ker

/-- The solution-valued propagator has the same kernel as its unrestricted counterpart. -/
lemma toSolutionSpace_ker :
    LinearMap.ker G.toSolutionSpace = LinearMap.ker G.causalPropagator := by
  ext f
  change (G.toSolutionSpace f = 0) ↔ G.causalPropagator f = 0
  exact Subtype.ext_iff
end

end GreenOperator.GreenOperators

namespace LocalOperator

section
variable {𝕜 M V : Type*} [Ring 𝕜] [TopologicalSpace M] [AddCommGroup V] [Module 𝕜 V] {S : Submodule
    𝕜 (M → V)} (P : LocalOperator S) (C : CausalRelation M)

/-- Every two future-supported fields with the same equation coincide. -/
lemma futureSupported_unique (h : Function.Injective (P.futureSupportedOperator C))
    {u v : S} (hu : u ∈ P.futureSupportedFields C) (hv : v ∈ P.futureSupportedFields C)
    (heq : P.operator u = P.operator v) : u = v := by
  have hsub : (⟨u, hu⟩ : P.futureSupportedFields C) = ⟨v, hv⟩ :=
    h (Subtype.ext heq)
  exact congrArg Subtype.val hsub

/-- Temporal cutoff splitting of spacelike-compact admissible fields.
In a smooth spacetime this is proved using a suitable smooth Cauchy cutoff and its complement.
It contains no Green-operator or solution-surjectivity assertion. -/
def HasCausalCutoffs : Prop :=
  ∀ u : P.spacelikeCompactFields C,
    ∃ uPlus : P.futureSupportedFields C,
    ∃ uMinus : P.futureSupportedFields C.reverse, (uPlus : S) - (uMinus : S) = u.val
end

end LocalOperator

namespace GreenOperator.GreenOperators

open LocalOperator

section
variable {𝕜 M V : Type*} [Ring 𝕜] [TopologicalSpace M] [AddCommGroup V] [Module 𝕜 V] {S : Submodule
    𝕜 (M → V)} {C : CausalRelation M} {P : LocalOperator S} (G : GreenOperators C P)

/-- Retarded compact-source responses belong to the extension's support class. -/
lemma retarded_mem_futureSupportedFields (f : P.compactSources) :
    G.retarded.toLinearMap f ∈ P.futureSupportedFields C :=
  ⟨tsupport (f.val : M → V), f.property, G.retarded.support f⟩

/-- Advanced compact-source responses belong to the past-supported extension class. -/
lemma advanced_mem_futureSupportedFields_reverse (f : P.compactSources) :
    G.advanced.toLinearMap f ∈ P.futureSupportedFields C.reverse :=
  ⟨tsupport (f.val : M → V), f.property, G.advanced.support f⟩

/-- One-sided uniqueness identifies any future-supported solution with the retarded response. -/
lemma retarded_eq_of_futureSupported (h : Function.Injective (P.futureSupportedOperator C))
    (f : P.compactSources) {u : S} (hu : u ∈ P.futureSupportedFields C)
    (hPu : P.operator u = f.val) : G.retarded.toLinearMap f = u :=
  P.futureSupported_unique C h (G.retarded_mem_futureSupportedFields f) hu
    ((G.retarded.solves f).trans hPu.symm)

/-- One-sided uniqueness identifies any past-supported solution with the advanced response. -/
lemma advanced_eq_of_pastSupported (h : Function.Injective (P.futureSupportedOperator C.reverse))
    (f : P.compactSources) {u : S} (hu : u ∈ P.futureSupportedFields C.reverse)
    (hPu : P.operator u = f.val) : G.advanced.toLinearMap f = u :=
  P.futureSupported_unique C.reverse h (G.advanced_mem_futureSupportedFields_reverse f) hu
    ((G.advanced.solves f).trans hPu.symm)
end

end GreenOperator.GreenOperators

namespace GreenOperator.RetardedGreenOperator

open LocalOperator

section
variable {𝕜 M V : Type*} [Ring 𝕜] [TopologicalSpace M] [AddCommGroup V] [Module 𝕜 V] {S : Submodule
    𝕜 (M → V)}
variable {C : CausalRelation M} {P : LocalOperator S} (G : RetardedGreenOperator C P)

/-- A compact source unable to reach the observation event has zero retarded response there. -/
lemma eq_zero_of_no_causal_source (f : P.compactSources) {x : M}
    (h : ∀ y : M, C.Precedes y x → y ∉ tsupport (f.val : M → V)) :
    (G.toLinearMap f : M → V) x = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro hx
  obtain ⟨y, hy, hyx⟩ := G.support f hx
  exact h y hyx hy

/-- Two compact-source responses coincide when their discrepancy cannot reach the observation
event. -/
lemma eq_of_no_causal_difference (f g : P.compactSources) {x : M}
    (h : ∀ y : M, C.Precedes y x → y ∉ tsupport ((f.val - g.val : S) : M → V)) :
    (G.toLinearMap f : M → V) x = (G.toLinearMap g : M → V) x := by
  have hz := G.eq_zero_of_no_causal_source (f - g) h
  apply sub_eq_zero.mp
  exact (congrArg (fun u : S => (u : M → V) x) (G.toLinearMap.map_sub f g)).symm.trans hz

/-- Compact truncations agreeing with the same field in the observation's causal past give
identical retarded responses. Equality is needed as germs to control topological support. -/
lemma eq_of_local_truncations (f g : P.compactSources) (u : S) {x : M}
    (hf : ∀ y : M, C.Precedes y x → (f.val : M → V) =ᶠ[𝓝 y] (u : M → V))
    (hg : ∀ y : M, C.Precedes y x → (g.val : M → V) =ᶠ[𝓝 y] (u : M → V)) :
    (G.toLinearMap f : M → V) x = (G.toLinearMap g : M → V) x := by
  apply G.eq_of_no_causal_difference f g
  intro y hyx
  exact notMem_tsupport_sub_iff_eventuallyEq.mpr ((hf y hyx).trans (hg y hyx).symm)
end

end GreenOperator.RetardedGreenOperator
