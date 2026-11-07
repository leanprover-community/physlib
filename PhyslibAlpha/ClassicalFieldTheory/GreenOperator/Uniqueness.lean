/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Analysis.Distribution.Support
public import PhyslibAlpha.ClassicalFieldTheory.GreenOperator.Localization

/-!

# Uniqueness and the causal exact sequence

## i. Overview

Existence and uniqueness of retarded solutions and the exact sequence of compact sources and
spacelike compact fields.

## ii. Key results

- `sourceOfCausalSplit` : The compact source obtained from a causal splitting of a homogeneous
  field.
- `solutionSpaceEquivQuotient` : Compact test fields modulo the equation of motion are equivalent to
  spacelike-compact homogeneous solutions.
- `solutionSpaceEquivQuotientOfLocalization` : Homogeneous spacelike-compact solutions are source
  classes, with one-sided inverse and uniqueness hypotheses discharged by local compact
  constructions.
- `toSpacelikeCompact` : The causal propagator with the support codomain required in the exact
  sequence.

## iii. Table of contents

- A. One-sided uniqueness for weak solutions
- B. Homogeneous solutions as source classes
- C. The causal Green exact sequence
- D. General sourced field equations

## iv. References

None.

## A. One-sided uniqueness for weak solutions

Lemmas: `distribution_eq_zero_of_retarded`.

## B. Homogeneous solutions as source classes

- `sourceOfCausalSplit` : The compact source obtained from a causal splitting of a homogeneous
  field.
- `solutionSpaceEquivQuotient` : Compact test fields modulo the equation of motion are equivalent to
  spacelike-compact homogeneous solutions.
- `solutionSpaceEquivQuotientOfLocalization` : Homogeneous spacelike-compact solutions are source
  classes, with one-sided inverse and uniqueness hypotheses discharged by local compact
  constructions.

Lemmas: `compact_equation_of_causal_split`, `causalPropagator_sourceOfCausalSplit`,
`toSolutionSpace_surjective`, `solutionSpaceEquivQuotient_symm_mk`,
`solutionSpaceEquivQuotient_toSolutionSpace`, `spacelikeCompactOperator_surjective_of_localization`.

## C. The causal Green exact sequence

- `toSpacelikeCompact` : The causal propagator with the support codomain required in the exact
  sequence.

Lemmas: `toSpacelikeCompact_ker`, `exact_compactSources`, `exact_spacelikeCompactFields`,
`causalGreen_exactSequence`.

## D. General sourced field equations

Lemmas: `existsUnique_retardedSolution`, `existsUnique_retardedSolution_of_localization`.

-/

@[expose] public section

noncomputable section

open CausalRelation LocalOperator Topology TopologicalSpace Submodule

namespace GreenOperator

section
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace
    ℝ V] {S : Submodule ℝ (E → ℝ)} {P : LocalOperator S} {C : CausalRelation E}

/-- Compact advanced Green data and causal localization force a retarded weak homogeneous
solution to vanish. The native test model preserves the underlying scalar test fields. -/
lemma distribution_eq_zero_of_retarded
    (e : P.compactSources ≃ₗ[ℝ] _root_.TestFunction (⊤ : Opens E) ℝ ⊤)
    (he : ∀ f : P.compactSources, (e f : E → ℝ) = f.val.val)
    (G : AdvancedGreenOperator C P) (L : PastLocalization C.reverse P)
    (hC : C.HasCompactCausalDiamonds) (K : Set E) (hK : IsCompact K)
    (T : Distribution (⊤ : Opens E) V ⊤)
    (hT : Distribution.IsVanishingOn T (C.causalFuture K)ᶜ)
    (hzero : ∀ f : P.compactSources, T (e (P.compactOperator f)) = 0) : T = 0 := by
  ext φ
  let f : P.compactSources := e.symm φ
  have hu : G.toLinearMap f ∈ P.pastCompactFields C.reverse :=
    P.futureSupportedFields_le_pastCompactFields C.reverse
      (HasCompactCausalDiamonds.reverse C hC)
      ⟨tsupport (f.val : E → ℝ), f.property, G.support f⟩
  let u : P.pastCompactFields C.reverse := ⟨G.toLinearMap f, hu⟩
  let ψ : P.compactSources := L.truncate u K hK
  let r : P.compactSources := P.compactOperator ψ - f
  have hr : tsupport (e r : E → ℝ) ⊆ (C.causalFuture K)ᶜ := by
    intro x hx hxK
    have hnot : x ∉ tsupport (e r : E → ℝ) := by
      apply notMem_tsupport_iff_eventuallyEq.mpr
      rw [he]
      have hloc := P.operator_eventuallyEq (L.truncate_agrees u K hK x hxK)
      have hus : P.operator u.val = f.val := G.solves f
      rw [hus] at hloc
      filter_upwards [hloc] with y hy
      change (P.operator ψ.val).val y - f.val.val y = 0
      exact sub_eq_zero.mpr hy
    exact hnot hx
  have hTr := hT (e r) hr
  change T (e (P.compactOperator ψ - f)) = 0 at hTr
  have her : e (P.compactOperator ψ - f) = e (P.compactOperator ψ) - e f :=
    e.toLinearMap.map_sub (P.compactOperator ψ) f
  have hTs : T (e (P.compactOperator ψ) - e f) = T (e (P.compactOperator ψ)) - T (e f) :=
    map_sub T (e (P.compactOperator ψ)) (e f)
  rw [her, hTs, hzero ψ, zero_sub, neg_eq_zero] at hTr
  change T φ = 0
  simpa only [f, e.apply_symm_apply] using hTr
end

end GreenOperator

namespace GreenOperator.GreenOperators

section
variable {𝕜 M V : Type*} [Ring 𝕜] [TopologicalSpace M] [AddCommGroup V] [Module 𝕜 V] {S : Submodule
    𝕜 (M → V)} {C : CausalRelation M} {P : LocalOperator S} (G : GreenOperators C P)

/-- Fix the inherited field addition for nested quotient inference. -/
local instance solutionFieldAddGroup : AddCommGroup S := S.addCommGroup

/-- Equal equations of a future-supported and a past-supported field have compact support. -/
lemma compact_equation_of_causal_split (hC : C.HasCompactCausalDiamonds)
    (uPlus : P.futureSupportedFields C) (uMinus : P.futureSupportedFields C.reverse)
    (heq : P.operator uPlus.val = P.operator uMinus.val) :
    HasCompactSupport (P.operator uPlus.val : M → V) := by
  obtain ⟨K, hK, hplus⟩ := uPlus.property
  obtain ⟨L, hL, hminus⟩ := uMinus.property
  apply (hC K L hK hL).of_isClosed_subset (isClosed_tsupport _)
  refine Set.subset_inter ((P.support_operator _).trans hplus) ?_
  rw [heq]
  exact (P.support_operator _).trans hminus

/-- The compact source obtained from a causal splitting of a homogeneous field. -/
def sourceOfCausalSplit (hC : C.HasCompactCausalDiamonds)
    (uPlus : P.futureSupportedFields C) (uMinus : P.futureSupportedFields C.reverse)
    (heq : P.operator uPlus.val = P.operator uMinus.val) : P.compactSources :=
  ⟨P.operator uPlus.val, compact_equation_of_causal_split hC uPlus uMinus heq⟩

/-- The causal propagator reconstructs the difference of a causal split from its common source. -/
lemma causalPropagator_sourceOfCausalSplit (hC : C.HasCompactCausalDiamonds)
    (hret : Function.Injective (P.futureSupportedOperator C))
    (hadv : Function.Injective (P.futureSupportedOperator C.reverse))
    (uPlus : P.futureSupportedFields C) (uMinus : P.futureSupportedFields C.reverse)
    (heq : P.operator uPlus.val = P.operator uMinus.val) :
    G.causalPropagator (sourceOfCausalSplit hC uPlus uMinus heq) = uPlus.val - uMinus.val := by
  change G.retarded.toLinearMap _ - G.advanced.toLinearMap _ = _
  rw [G.retarded_eq_of_futureSupported hret _ uPlus.property rfl,
    G.advanced_eq_of_pastSupported hadv _ uMinus.property heq.symm]

/-- Every spacelike-compact homogeneous field is produced by a compact source.
The source is constructed from a causal cutoff rather than postulated as a preimage. -/
lemma toSolutionSpace_surjective (hC : C.HasCompactCausalDiamonds)
    (hret : Function.Injective (P.futureSupportedOperator C)) (hadv : Function.Injective
      (P.futureSupportedOperator C.reverse))
    (hcut : P.HasCausalCutoffs C) : Function.Surjective G.toSolutionSpace := by
  intro u
  obtain ⟨uPlus, uMinus, hsplit⟩ := hcut ⟨u.val, u.property.1⟩
  have heq : P.operator uPlus.val = P.operator uMinus.val := by
    apply sub_eq_zero.mp
    rw [← map_sub, hsplit]
    exact u.property.2
  let f := sourceOfCausalSplit hC uPlus uMinus heq
  refine ⟨f, Subtype.ext ?_⟩
  exact (G.causalPropagator_sourceOfCausalSplit hC hret hadv uPlus uMinus heq).trans hsplit

/-- Compact test fields modulo the equation of motion are equivalent to spacelike-compact
homogeneous solutions. All support, cutoff and one-sided supported hypotheses are explicit. -/
noncomputable def solutionSpaceEquivQuotient (hC : C.HasCompactCausalDiamonds)
    (hret : Function.Injective (P.futureSupportedOperator C)) (hadv : Function.Injective
      (P.futureSupportedOperator C.reverse))
    (hcut : P.HasCausalCutoffs C) :
    P.spacelikeCompactSolution C ≃ₗ[𝕜]
      (P.compactSources ⧸ LinearMap.range P.compactOperator) :=
  ((Submodule.quotEquivOfEq _ _
      (G.toSolutionSpace_ker.trans (G.causalPropagator_ker hC)).symm).trans
    (G.toSolutionSpace.quotKerEquivOfSurjective
      (G.toSolutionSpace_surjective hC hret hadv hcut))).symm

/-- The quotient-to-solution map is exactly the causal propagator on each source class. -/
@[simp]
lemma solutionSpaceEquivQuotient_symm_mk (hC : C.HasCompactCausalDiamonds)
    (hret : Function.Injective (P.futureSupportedOperator C))
    (hadv : Function.Injective (P.futureSupportedOperator C.reverse))
    (hcut : P.HasCausalCutoffs C) (f : P.compactSources) :
    (G.solutionSpaceEquivQuotient hC hret hadv hcut).symm (Submodule.Quotient.mk f) =
      G.toSolutionSpace f := rfl

/-- A causally produced solution represents precisely the class of its source. -/
@[simp]
lemma solutionSpaceEquivQuotient_toSolutionSpace (hC : C.HasCompactCausalDiamonds)
    (hret : Function.Injective (P.futureSupportedOperator C))
    (hadv : Function.Injective (P.futureSupportedOperator C.reverse))
    (hcut : P.HasCausalCutoffs C) (f : P.compactSources) :
    G.solutionSpaceEquivQuotient hC hret hadv hcut (G.toSolutionSpace f) =
      Submodule.Quotient.mk f := by
  rw [← G.solutionSpaceEquivQuotient_symm_mk hC hret hadv hcut f]
  exact (G.solutionSpaceEquivQuotient hC hret hadv hcut).apply_symm_apply _

include G in
/-- The final equation map is onto by solving the two cutoff pieces with the constructed
extensions. -/
lemma spacelikeCompactOperator_surjective_of_localization
    (Lret : PastLocalization C P) (Ladv : PastLocalization C.reverse P)
    (hC : C.HasCompactCausalDiamonds) (hcut : P.HasCausalCutoffs C) :
    Function.Surjective (P.spacelikeCompactOperator C) := by
  intro f
  obtain ⟨fPlus, fMinus, hsplit⟩ := hcut f
  obtain ⟨uPlus, hp⟩ := Lret.futureSupportedOperator_surjective G.retarded hC fPlus
  obtain ⟨uMinus, hm⟩ := Ladv.futureSupportedOperator_surjective G.reverse.retarded
    (HasCompactCausalDiamonds.reverse C hC) fMinus
  refine ⟨⟨uPlus.val - uMinus.val, (P.spacelikeCompactFields C).sub_mem
    (P.futureSupportedFields_le_spacelikeCompactFields C uPlus.property)
    (P.pastSupportedFields_le_spacelikeCompactFields C uMinus.property)⟩, Subtype.ext ?_⟩
  change P.operator (uPlus.val - uMinus.val) = f.val
  have hpval : P.operator uPlus.val = fPlus.val := congrArg Subtype.val hp
  have hmval : P.operator uMinus.val = fMinus.val := congrArg Subtype.val hm
  rw [map_sub, hpval, hmval]
  exact hsplit

/-- Homogeneous spacelike-compact solutions are source classes, with one-sided inverse and
uniqueness hypotheses discharged by local compact constructions. -/
noncomputable def solutionSpaceEquivQuotientOfLocalization
    (Lret : PastLocalization C P) (Ladv : PastLocalization C.reverse P)
    (hC : C.HasCompactCausalDiamonds) (hcut : P.HasCausalCutoffs C) :
    P.spacelikeCompactSolution C ≃ₗ[𝕜]
      (P.compactSources ⧸ LinearMap.range P.compactOperator) :=
  G.solutionSpaceEquivQuotient hC
    (Lret.futureSupportedOperator_injective G.retarded hC)
    (Ladv.futureSupportedOperator_injective G.reverse.retarded
      (HasCompactCausalDiamonds.reverse C hC)) hcut

/-- The causal propagator with the support codomain required in the exact sequence. -/
def toSpacelikeCompact : P.compactSources →ₗ[𝕜] P.spacelikeCompactFields C :=
  G.causalPropagator.codRestrict _ (fun f => (G.causalPropagator_mem_solution f).1)

/-- The codomain restriction does not change the propagator's kernel. -/
lemma toSpacelikeCompact_ker :
    LinearMap.ker G.toSpacelikeCompact = LinearMap.ker G.causalPropagator := by
  ext f
  exact Subtype.ext_iff

/-- Exactness at compact sources in the support-typed causal sequence. -/
lemma exact_compactSources (hC : C.HasCompactCausalDiamonds) :
    Function.Exact P.compactOperator G.toSpacelikeCompact :=
  LinearMap.exact_iff.mpr ((G.toSpacelikeCompact_ker).trans (G.causalPropagator_ker hC))

/-- Exactness at spacelike-compact fields follows from causal splitting and one-sided uniqueness. -/
lemma exact_spacelikeCompactFields (hC : C.HasCompactCausalDiamonds)
    (hret : Function.Injective (P.futureSupportedOperator C))
    (hadv : Function.Injective (P.futureSupportedOperator C.reverse))
    (hcut : P.HasCausalCutoffs C) :
    Function.Exact G.toSpacelikeCompact (P.spacelikeCompactOperator C) := by
  apply LinearMap.exact_iff.mpr
  ext u
  constructor
  · intro hu
    have hu0 : P.operator u.val = 0 := congrArg Subtype.val hu
    obtain ⟨f, hf⟩ := G.toSolutionSpace_surjective hC hret hadv hcut
      ⟨u.val, u.property, hu0⟩
    have hfval : G.causalPropagator f = u.val :=
      congrArg (fun v : P.spacelikeCompactSolution C => v.val) hf
    exact ⟨f, Subtype.ext hfval⟩
  · rintro ⟨f, rfl⟩
    apply Subtype.ext
    exact G.causalPropagator_solves f

include G in
/-- The full causal Green sequence, including injectivity and terminal surjectivity.
The larger-support inverses and uniqueness are derived from compact Green data and localization. -/
lemma causalGreen_exactSequence
    (Lret : PastLocalization C P) (Ladv : PastLocalization C.reverse P)
    (hC : C.HasCompactCausalDiamonds) (hcut : P.HasCausalCutoffs C) :
    Function.Injective P.compactOperator ∧
      Function.Exact P.compactOperator G.toSpacelikeCompact ∧
      Function.Exact G.toSpacelikeCompact (P.spacelikeCompactOperator C) ∧
      Function.Surjective (P.spacelikeCompactOperator C) :=
  ⟨G.compactOperator_injective, G.exact_compactSources hC,
    G.exact_spacelikeCompactFields hC
      (Lret.futureSupportedOperator_injective G.retarded hC)
      (Ladv.futureSupportedOperator_injective G.reverse.retarded
        (HasCompactCausalDiamonds.reverse C hC)) hcut,
    G.spacelikeCompactOperator_surjective_of_localization Lret Ladv hC hcut⟩
end

end GreenOperator.GreenOperators

namespace GreenOperator.RetardedGreenOperator

section
variable {𝕜 M V : Type*} [Ring 𝕜] [TopologicalSpace M] [AddCommGroup V] [Module 𝕜 V] {S : Submodule
    𝕜 (M → V)} {C : CausalRelation M} {P : LocalOperator S}
variable (G : RetardedGreenOperator C P)

include G in
/-- A source has exactly one sharply retarded solution when the future-supported homogeneous
kernel vanishes. Existence follows from the supplied Green operator. -/
lemma existsUnique_retardedSolution
    (huniq : Function.Injective (P.futureSupportedOperator C)) (f : P.compactSources) :
    ∃! u : S, P.operator u = f.val ∧
      tsupport (u : M → V) ⊆ C.causalFuture (tsupport (f.val : M → V)) := by
  refine ⟨G.toLinearMap f, ⟨G.solves f, G.support f⟩, ?_⟩
  intro u hu
  exact P.futureSupported_unique C huniq
    ⟨tsupport (f.val : M → V), f.property, hu.2⟩
    ⟨tsupport (f.val : M → V), f.property, G.support f⟩
    (hu.1.trans (G.solves f).symm)

include G in
/-- Local compact-cutoff geometry proves the uniqueness hypothesis of the compact-source theorem. -/
lemma existsUnique_retardedSolution_of_localization (L : PastLocalization C P)
    (hC : C.HasCompactCausalDiamonds) (f : P.compactSources) :
    ∃! u : S, P.operator u = f.val ∧
      tsupport (u : M → V) ⊆ C.causalFuture (tsupport (f.val : M → V)) :=
  G.existsUnique_retardedSolution (L.futureSupportedOperator_injective G hC) f
end

end GreenOperator.RetardedGreenOperator
