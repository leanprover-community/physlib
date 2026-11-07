/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import PhyslibAlpha.ClassicalFieldTheory.GreenOperator.Basic
public import PhyslibAlpha.ClassicalFieldTheory.GreenOperator.CausalPropagator

/-!

# Localization and extension of retarded responses

A past compact source is cut off to compact pieces.

## i. Overview

A past compact source is cut off to compact pieces. The retarded responses to the pieces define a
response to the whole source.

## ii. Key results

- `PastLocalization` : The geometric and cutoff data for localizing past-compact sections to compact
  test sections.
- `sourceAt` : Each source has a compact truncation adapted to the observation event.
- `retardedValue` : The pointwise retarded response obtained from observation-adapted compact
  truncations.
- `retardedSection` : The glued retarded field as an admissible section.
- `retardedExtension` : The two-sided linear Green extension to all past-compact sources.
- `truncationRadius` : A positive ball radius enclosing the relevant compact part of the source.
- `truncationBump` : A smooth compact bump equal to one near the relevant source intersection.
- `bumpTruncate` : A bump truncation is a compact admissible source, not an assumed larger-support
  solution.

## iii. Table of contents

- A. Compact localization of past-compact sources
- B. Constructing Green extensions by local compact truncation
- C. Compact source localization by smooth bump functions

## iv. References

None.

## A. Compact localization of past-compact sources

- `PastLocalization` : The geometric and cutoff data for localizing past-compact sections to compact
  test sections.
- `sourceAt` : Each source has a compact truncation adapted to the observation event.
- `retardedValue` : The pointwise retarded response obtained from observation-adapted compact
  truncations.

Lemmas: `mem_past_bound`, `sourceAt_agrees`, `predecessor_mem_past_bound`,
`retardedValue_eq_on_past_bound`, `retardedValue_eventuallyEq`, `retardedValue_mem`,
`homogeneous_eq_zero`, `pastCompactOperator_injective`.

## B. Constructing Green extensions by local compact truncation

- `retardedSection` : The glued retarded field as an admissible section.
- `retardedExtension` : The two-sided linear Green extension to all past-compact sources.

Lemmas: `retardedSection_solves`, `retardedValue_support`, `retardedSection_support`,
`retardedSection_mem_pastCompactFields`, `pastCompactOperator_surjective`,
`retardedExtension_solves`, `retardedExtension_eq_section`, `retardedExtension_support`,
`pastCompact_unique`, `futureSupportedOperator_injective` and more.

## C. Compact source localization by smooth bump functions

- `truncationRadius` : A positive ball radius enclosing the relevant compact part of the source.
- `truncationBump` : A smooth compact bump equal to one near the relevant source intersection.
- `bumpTruncate` : A bump truncation is a compact admissible source, not an assumed larger-support
  solution.
- `ofBumpFunctions` : Construct all local compact-source truncation data from bump stability and
  causal topology.

Lemmas: `truncationRadius_pos`, `mem_truncation_ball`, `bumpTruncate_support`,
`bumpTruncate_agrees`.

-/

@[expose] public section

noncomputable section

open scoped Topology
open CausalRelation LocalOperator Topology

namespace GreenOperator

section
variable {𝕜 M V : Type*} [Ring 𝕜] [TopologicalSpace M] [AddCommGroup V] [Module 𝕜 V] {S : Submodule
    𝕜 (M → V)}

/-- The geometric and cutoff data for localizing past-compact sections to compact test sections. -/
structure PastLocalization (C : CausalRelation M) (P : LocalOperator S) where
  /-- Compact observation bounds whose causal pasts are neighborhoods. -/
  bound : M → Set M
  /-- Every observation bound is compact. -/
  bound_compact : ∀ x, IsCompact (bound x)
  /-- The causal past of an observation bound contains a neighborhood of the event. -/
  bound_neighborhood : ∀ x, C.causalPast (bound x) ∈ 𝓝 x
  /-- Admissible fields glue from local representatives. -/
  local_fields : IsLocalFieldSpace S
  /-- The causal future of a compact set is closed. -/
  closed_compact_future : ∀ K : Set M, IsCompact K → IsClosed (C.causalFuture K)
  /-- Compact source truncation near the causal past of a compact observation set. -/
  truncate : P.pastCompactFields C → (K : Set M) → IsCompact K → P.compactSources
  /-- Truncation agrees as germs with the source throughout that causal past. -/
  truncate_agrees : ∀ f K hK x, x ∈ C.causalPast K →
    ((truncate f K hK).val : M → V) =ᶠ[𝓝 x] (f.val : M → V)
  /-- Compact truncation introduces no support outside the original source. -/
  truncate_support : ∀ f K hK,
    tsupport ((truncate f K hK).val : M → V) ⊆ tsupport (f.val : M → V)
end

end GreenOperator

namespace GreenOperator.PastLocalization

section
variable {𝕜 M V : Type*} [Ring 𝕜] [TopologicalSpace M] [AddCommGroup V] [Module 𝕜 V] {S : Submodule
    𝕜 (M → V)}
variable {C : CausalRelation M} {P : LocalOperator S} (L : PastLocalization C P)

lemma mem_past_bound (x : M) : x ∈ C.causalPast (L.bound x) :=
  mem_of_mem_nhds (L.bound_neighborhood x)

/-- Each source has a compact truncation adapted to the observation event. -/
def sourceAt (f : P.pastCompactFields C) (x : M) : P.compactSources :=
  L.truncate f (L.bound x) (L.bound_compact x)

lemma sourceAt_agrees (f : P.pastCompactFields C) (x : M) {y : M}
    (hy : y ∈ C.causalPast (L.bound x)) :
    ((L.sourceAt f x).val : M → V) =ᶠ[𝓝 y] (f.val : M → V) :=
  L.truncate_agrees f _ _ y hy

lemma predecessor_mem_past_bound {x y : M} (hyx : C.Precedes y x) :
    y ∈ C.causalPast (L.bound x) := by
  obtain ⟨z, hz, hxz⟩ := L.mem_past_bound x
  exact ⟨z, hz, C.trans hyx hxz⟩

/-- The pointwise retarded response obtained from observation-adapted compact truncations. -/
def retardedValue (G : RetardedGreenOperator C P) (f : P.pastCompactFields C) : M → V :=
  fun x => (G.toLinearMap (L.sourceAt f x) : M → V) x

/-- Retarded responses of different admissible truncations agree locally.
No limit or convergence of the truncation family is required. -/
lemma retardedValue_eq_on_past_bound (G : RetardedGreenOperator C P)
    (f : P.pastCompactFields C) (x : M) {y : M}
    (hy : y ∈ C.causalPast (L.bound x)) :
    L.retardedValue G f y = (G.toLinearMap (L.sourceAt f x) : M → V) y := by
  apply G.eq_of_local_truncations (L.sourceAt f y) (L.sourceAt f x) f.val
  · intro z hzy
    exact L.sourceAt_agrees f y (L.predecessor_mem_past_bound hzy)
  · intro z hzy
    obtain ⟨k, hk, hyk⟩ := hy
    exact L.sourceAt_agrees f x ⟨k, hk, C.trans hzy hyk⟩

/-- Near any event the response is an ordinary compact-source Green response. -/
lemma retardedValue_eventuallyEq (G : RetardedGreenOperator C P)
    (f : P.pastCompactFields C) (x : M) :
    L.retardedValue G f =ᶠ[𝓝 x] (G.toLinearMap (L.sourceAt f x) : M → V) := by
  filter_upwards [L.bound_neighborhood x] with y hy
  exact L.retardedValue_eq_on_past_bound G f x hy

/-- The pointwise construction is admissible by local gluing. -/
lemma retardedValue_mem (G : RetardedGreenOperator C P) (f : P.pastCompactFields C) :
    L.retardedValue G f ∈ S :=
  L.local_fields _ (fun x => ⟨G.toLinearMap (L.sourceAt f x), L.retardedValue_eventuallyEq G f x⟩)

include L in
/-- A past-compact homogeneous field vanishes, proved from compact Green identities and cutoffs. -/
lemma homogeneous_eq_zero (G : RetardedGreenOperator C P) (u : P.pastCompactFields C)
    (hPu : P.operator u.val = 0) : u.val = 0 := by
  apply Subtype.ext
  funext x
  let a := L.sourceAt u x
  have hzero : (G.toLinearMap (P.compactOperator a) : M → V) x = 0 := by
    apply G.eq_zero_of_no_causal_source
    intro y hyx
    have hagree := L.sourceAt_agrees u x (L.predecessor_mem_past_bound hyx)
    have hPagree := P.operator_eventuallyEq hagree
    rw [hPu] at hPagree
    exact notMem_tsupport_iff_eventuallyEq.mpr hPagree
  rw [G.comp_operator] at hzero
  have hagree := L.sourceAt_agrees u x (L.mem_past_bound x)
  exact hagree.eq_of_nhds.symm.trans hzero

include L in
/-- One-sided uniqueness is a consequence of local compact truncation and the compact Green
inverse. -/
lemma pastCompactOperator_injective (G : RetardedGreenOperator C P) :
    Function.Injective (P.pastCompactOperator C) := by
  intro u v huv
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply L.homogeneous_eq_zero G (u - v)
  change P.operator (u.val - v.val) = 0
  rw [map_sub]
  exact sub_eq_zero.mpr (congrArg Subtype.val huv)
end

section
variable {𝕜 M V : Type*} [Ring 𝕜] [TopologicalSpace M] [AddCommGroup V] [Module 𝕜 V] {S : Submodule
    𝕜 (M → V)} {C : CausalRelation M} {P : LocalOperator S} (L : PastLocalization C P) (G :
    RetardedGreenOperator C P)

/-- The glued retarded field as an admissible section. -/
def retardedSection (f : P.pastCompactFields C) : S :=
  ⟨L.retardedValue G f, L.retardedValue_mem G f⟩

/-- The glued field solves the full past-compact source equation. -/
lemma retardedSection_solves (f : P.pastCompactFields C) :
    P.operator (L.retardedSection G f) = f.val := by
  apply Subtype.ext
  funext x
  have hlocal := P.operator_eq_of_eventuallyEq
    (u := L.retardedSection G f) (v := G.toLinearMap (L.sourceAt f x))
    (L.retardedValue_eventuallyEq G f x)
  have hsolve := congrArg (fun u : S => (u : M → V) x) (G.solves (L.sourceAt f x))
  exact hlocal.trans (hsolve.trans (L.sourceAt_agrees f x (L.mem_past_bound x)).eq_of_nhds)

/-- Pointwise support of the glued response lies in the future of the source. -/
lemma retardedValue_support (f : P.pastCompactFields C) :
    Function.support (L.retardedValue G f) ⊆ C.causalFuture (tsupport (f.val : M → V)) := by
  intro x hx
  have hresp : x ∈ tsupport (G.toLinearMap (L.sourceAt f x) : M → V) :=
    subset_tsupport _ hx
  exact C.causalFuture_mono (L.truncate_support f _ _) (G.support _ hresp)

/-- The topological support bound follows from the closed future of a past-compact source. -/
lemma retardedSection_support (f : P.pastCompactFields C) :
    tsupport (L.retardedSection G f : M → V) ⊆ C.causalFuture (tsupport (f.val : M → V)) := by
  apply closure_minimal (L.retardedValue_support G f)
  exact IsPastCompact.isClosed_causalFuture C L.closed_compact_future
    (fun x => ⟨L.bound x, L.bound_compact x, L.bound_neighborhood x⟩) f.property

/-- Causal support and compact diamonds put the constructed response in the full past-compact
class. -/
lemma retardedSection_mem_pastCompactFields (hC : C.HasCompactCausalDiamonds)
    (f : P.pastCompactFields C) : L.retardedSection G f ∈ P.pastCompactFields C :=
  IsPastCompact.mono C
    (IsPastCompact.causalFuture C hC f.property)
    (isClosed_tsupport _) (L.retardedSection_support G f)

include L G in
/-- Existence on the larger support class is constructed from local compact responses. -/
lemma pastCompactOperator_surjective (hC : C.HasCompactCausalDiamonds) :
    Function.Surjective (P.pastCompactOperator C) := by
  intro f
  exact ⟨⟨L.retardedSection G f, L.retardedSection_mem_pastCompactFields G hC f⟩,
    Subtype.ext (L.retardedSection_solves G f)⟩

/-- The two-sided linear Green extension to all past-compact sources. -/
noncomputable def retardedExtension (hC : C.HasCompactCausalDiamonds) :
    P.pastCompactFields C ≃ₗ[𝕜] P.pastCompactFields C :=
  (LinearEquiv.ofBijective (P.pastCompactOperator C)
    ⟨L.pastCompactOperator_injective G, L.pastCompactOperator_surjective G hC⟩).symm

/-- The constructed extension solves the source equation. -/
lemma retardedExtension_solves (hC : C.HasCompactCausalDiamonds) (f : P.pastCompactFields C) :
    P.pastCompactOperator C (L.retardedExtension G hC f) = f :=
  (LinearEquiv.ofBijective (P.pastCompactOperator C)
    ⟨L.pastCompactOperator_injective G, L.pastCompactOperator_surjective G hC⟩).apply_symm_apply f

/-- The abstract linear inverse equals the explicitly glued local response. -/
lemma retardedExtension_eq_section (hC : C.HasCompactCausalDiamonds)
    (f : P.pastCompactFields C) :
    (L.retardedExtension G hC f).val = L.retardedSection G f := by
  have heq : L.retardedExtension G hC f =
      ⟨L.retardedSection G f, L.retardedSection_mem_pastCompactFields G hC f⟩ := by
    apply L.pastCompactOperator_injective G
    exact (L.retardedExtension_solves G hC f).trans
      (Subtype.ext (L.retardedSection_solves G f)).symm
  exact congrArg Subtype.val heq

/-- The full past-compact extension retains the sharp causal support bound. -/
lemma retardedExtension_support (hC : C.HasCompactCausalDiamonds) (f : P.pastCompactFields C) :
    tsupport ((L.retardedExtension G hC f).val : M → V) ⊆
      C.causalFuture (tsupport (f.val : M → V)) := by
  rw [L.retardedExtension_eq_section G hC f]
  exact L.retardedSection_support G f

include L G in
/-- Uniqueness for admissible fields in the full past-compact class. -/
lemma pastCompact_unique {u v : S}
    (hu : u ∈ P.pastCompactFields C) (hv : v ∈ P.pastCompactFields C)
    (heq : P.operator u = P.operator v) : u = v := by
  have h : (⟨u, hu⟩ : P.pastCompactFields C) = ⟨v, hv⟩ :=
    L.pastCompactOperator_injective G (Subtype.ext heq)
  exact congrArg Subtype.val h

include L G in
/-- One-sided uniqueness on compactly generated future support is now a theorem. -/
lemma futureSupportedOperator_injective (hC : C.HasCompactCausalDiamonds) :
    Function.Injective (P.futureSupportedOperator C) := by
  intro u v huv
  apply Subtype.ext
  apply L.pastCompact_unique G
    (P.futureSupportedFields_le_pastCompactFields C hC u.property)
    (P.futureSupportedFields_le_pastCompactFields C hC v.property)
  exact congrArg Subtype.val huv

/-- The extension preserves support in the future of any one compact source bound. -/
lemma retardedExtension_mem_futureSupportedFields (hC : C.HasCompactCausalDiamonds)
    (f : P.futureSupportedFields C) :
    (L.retardedExtension G hC
      ⟨f.val, P.futureSupportedFields_le_pastCompactFields C hC f.property⟩).val ∈
      P.futureSupportedFields C := by
  obtain ⟨K, hK, hfK⟩ := f.property
  refine ⟨K, hK, ?_⟩
  have hs := (L.retardedExtension_support G hC
    ⟨f.val, P.futureSupportedFields_le_pastCompactFields C hC f.property⟩).trans
    (C.causalFuture_mono hfK)
  simpa only [C.causalFuture_idem] using hs

include L G in
/-- Solvability on compactly generated future support is proved by restricting the constructed
past-compact extension. It is not an additional existence assumption. -/
lemma futureSupportedOperator_surjective (hC : C.HasCompactCausalDiamonds) :
    Function.Surjective (P.futureSupportedOperator C) := by
  intro f
  let fp : P.pastCompactFields C :=
    ⟨f.val, P.futureSupportedFields_le_pastCompactFields C hC f.property⟩
  have hs : P.operator (L.retardedExtension G hC fp).val = f.val :=
    congrArg (fun u : P.pastCompactFields C => u.val) (L.retardedExtension_solves G hC fp)
  exact ⟨⟨(L.retardedExtension G hC fp).val,
    L.retardedExtension_mem_futureSupportedFields G hC f⟩, Subtype.ext hs⟩
end

section
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [AddCommGroup V] [Module ℝ V] {S : Submodule ℝ (E → V)} {P : LocalOperator S} {C :
    CausalRelation E} (hmul : ∀ (b : ContDiffBump (0 : E)) (u : S), (fun x => b x • u.val x) ∈ S)

/-- A positive ball radius enclosing the relevant compact part of the source. -/
def truncationRadius (f : P.pastCompactFields C) (K : Set E) (hK : IsCompact K) : ℝ :=
  Classical.choose ((f.property K hK).isBounded.exists_pos_norm_lt)

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
lemma truncationRadius_pos (f : P.pastCompactFields C) (K : Set E) (hK : IsCompact K) :
    0 < truncationRadius f K hK :=
  (Classical.choose_spec ((f.property K hK).isBounded.exists_pos_norm_lt)).1

/-- A smooth compact bump equal to one near the relevant source intersection. -/
def truncationBump (f : P.pastCompactFields C) (K : Set E) (hK : IsCompact K) :
    ContDiffBump (0 : E) where
  rIn := truncationRadius f K hK
  rOut := truncationRadius f K hK + 1
  rIn_pos := truncationRadius_pos f K hK
  rIn_lt_rOut := lt_add_one _

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
lemma mem_truncation_ball (f : P.pastCompactFields C) (K : Set E) (hK : IsCompact K)
    {x : E} (hx : x ∈ tsupport (f.val : E → V)) (hp : x ∈ C.causalPast K) :
    x ∈ Metric.ball (0 : E) (truncationBump f K hK).rIn := by
  rw [Metric.mem_ball, dist_zero_right]
  exact (Classical.choose_spec ((f.property K hK).isBounded.exists_pos_norm_lt)).2 x ⟨hx, hp⟩

/-- A bump truncation is a compact admissible source, not an assumed larger-support solution. -/
def bumpTruncate (f : P.pastCompactFields C) (K : Set E) (hK : IsCompact K) :
    P.compactSources :=
  ⟨⟨fun x => truncationBump f K hK x • (f.val : E → V) x,
    hmul (truncationBump f K hK) f.val⟩,
    (truncationBump f K hK).hasCompactSupport.of_isClosed_subset (isClosed_tsupport _)
      (tsupport_smul_subset_left _ _)⟩

/-- Truncating by multiplication introduces no support outside the source. -/
lemma bumpTruncate_support (f : P.pastCompactFields C) (K : Set E) (hK : IsCompact K) :
    tsupport ((bumpTruncate hmul f K hK).val : E → V) ⊆ tsupport (f.val : E → V) :=
  tsupport_smul_subset_right _ _

/-- The truncation agrees as germs on the entire causal past of the observation set. -/
lemma bumpTruncate_agrees (f : P.pastCompactFields C) (K : Set E) (hK : IsCompact K)
    (x : E) (hx : x ∈ C.causalPast K) :
    ((bumpTruncate hmul f K hK).val : E → V) =ᶠ[𝓝 x] (f.val : E → V) := by
  by_cases hs : x ∈ tsupport (f.val : E → V)
  · have hb := (truncationBump f K hK).eventuallyEq_one_of_mem_ball
      (mem_truncation_ball f K hK hs hx)
    filter_upwards [hb] with y hy
    change truncationBump f K hK y • (f.val : E → V) y = _
    rw [hy]
    exact one_smul ℝ _
  · have hf := notMem_tsupport_iff_eventuallyEq.mp hs
    filter_upwards [hf] with y hy
    change truncationBump f K hK y • (f.val : E → V) y = _
    rw [hy]
    exact smul_zero _

/-- Construct all local compact-source truncation data from bump stability and causal topology.
No existence or uniqueness of a Green response is an input. -/
def ofBumpFunctions (hlocal : IsLocalFieldSpace S)
    (hclosed : ∀ K : Set E, IsCompact K → IsClosed (C.causalFuture K))
    (hbound : ∀ x : E, ∃ K : Set E, IsCompact K ∧ C.causalPast K ∈ 𝓝 x) :
    PastLocalization C P where
  bound x := Classical.choose (hbound x)
  bound_compact x := (Classical.choose_spec (hbound x)).1
  bound_neighborhood x := (Classical.choose_spec (hbound x)).2
  local_fields := hlocal
  closed_compact_future := hclosed
  truncate := bumpTruncate hmul
  truncate_agrees := bumpTruncate_agrees hmul
  truncate_support := bumpTruncate_support hmul
end

end GreenOperator.PastLocalization
