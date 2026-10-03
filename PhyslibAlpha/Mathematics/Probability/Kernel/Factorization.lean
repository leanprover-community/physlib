/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated

/-!
# Factorization of Markov kernels

Factoring kernels through Markov kernels, almost everywhere variants, and common refinements.

## i. Overview

A kernel `K : α → β` factors through a kernel `L : α → γ` when `K = κ ∘ₖ L` for some Markov kernel
`κ : γ → β`. Factoring through is a preorder on kernels with a common source; the target spaces
may differ. Relative to a measure `μ` on the source it suffices that the factorization holds at
`μ`-almost every point, and on a countably generated target, kernels that agree almost everywhere
on each measurable set agree almost everywhere. Two kernels have a common refinement when both
factor through a third one.

## ii. Key results

- `ProbabilityTheory.Kernel.FactorsThrough` : `K = κ ∘ₖ L` for a Markov kernel `κ`.
- `ProbabilityTheory.Kernel.MutuallyFactor` : factoring in both directions.
- `ProbabilityTheory.Kernel.FactorsThroughAE` : factoring at almost every point.
- `ProbabilityTheory.Kernel.ae_eq_of_forall_ae_apply_eq` : on a countably generated target,
  kernels that agree almost everywhere on each measurable set agree almost everywhere.
- `ProbabilityTheory.Kernel.HaveCommonRefinement` : both kernels factor through a third one.

## iii. Table of contents

- A. Factorization
- B. Mutual factorization
- C. Factorization almost everywhere
- D. Mutual factorization almost everywhere
- E. Kernels equal almost everywhere
- F. Common refinements

## iv. References

* None.

-/

@[expose] public section

open MeasureTheory
open scoped ProbabilityTheory

namespace ProbabilityTheory.Kernel

universe u v w z

section Factorization

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type z}
  [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]

/-! ## A. Factorization -/

/-- `K` factors through `L`: `K = κ ∘ₖ L` for a Markov kernel `κ`. -/
def FactorsThrough (K : Kernel α β) (L : Kernel α γ) : Prop :=
  ∃ κ : Kernel γ β, IsMarkovKernel κ ∧ K = κ ∘ₖ L

/-- Every kernel factors through itself. -/
lemma factorsThrough_refl (K : Kernel α β) : FactorsThrough K K :=
  ⟨Kernel.id, inferInstance, (Kernel.id_comp K).symm⟩

/-- Factoring through a kernel is transitive. -/
lemma factorsThrough_trans {K : Kernel α β} {L : Kernel α γ} {M : Kernel α δ}
    (hKL : FactorsThrough K L) (hLM : FactorsThrough L M) : FactorsThrough K M := by
  obtain ⟨κ, hκ, rfl⟩ := hKL
  obtain ⟨η, hη, rfl⟩ := hLM
  exact ⟨κ ∘ₖ η, inferInstance, (Kernel.comp_assoc κ η M).symm⟩

/-- If `K` factors through `L`, each measure `K a` is the bind of `L a` with a Markov kernel. -/
lemma factorsThrough_apply {K : Kernel α β} {L : Kernel α γ}
    (h : FactorsThrough K L) (a : α) :
    ∃ κ : Kernel γ β, IsMarkovKernel κ ∧ K a = (L a).bind κ := by
  obtain ⟨κ, hκ, rfl⟩ := h
  exact ⟨κ, hκ, Kernel.comp_apply κ L a⟩

/-- A constant kernel with a probability measure factors through every Markov kernel. -/
lemma const_factorsThrough (K : Kernel α γ) [IsMarkovKernel K]
    (μ : MeasureTheory.Measure β) [MeasureTheory.IsProbabilityMeasure μ] :
    FactorsThrough (Kernel.const α μ) K := by
  exact ⟨Kernel.const γ μ, inferInstance, (Kernel.const_comp' μ K).symm⟩

/-! ## B. Mutual factorization -/

/-- Two kernels factor through each other. -/
def MutuallyFactor (K : Kernel α β) (L : Kernel α γ) : Prop :=
  FactorsThrough K L ∧ FactorsThrough L K

/-- Mutual factoring is reflexive. -/
lemma mutuallyFactor_refl (K : Kernel α β) : MutuallyFactor K K :=
  ⟨factorsThrough_refl K, factorsThrough_refl K⟩

/-- Mutual factoring is symmetric. -/
lemma mutuallyFactor_symm {K : Kernel α β} {L : Kernel α γ}
    (h : MutuallyFactor K L) : MutuallyFactor L K :=
  h.symm

/-- Mutual factoring is transitive. -/
lemma mutuallyFactor_trans {K : Kernel α β} {L : Kernel α γ} {M : Kernel α δ}
    (hKL : MutuallyFactor K L) (hLM : MutuallyFactor L M) : MutuallyFactor K M :=
  ⟨factorsThrough_trans hKL.1 hLM.1, factorsThrough_trans hLM.2 hKL.2⟩

/-! ## C. Factorization almost everywhere -/

/-- `K` factors through `L` at `μ`-almost every point: `K =ᵐ[μ] κ ∘ₖ L` for a Markov kernel `κ`. -/
def FactorsThroughAE (μ : Measure α) (K : Kernel α β) (L : Kernel α γ) : Prop :=
  ∃ κ : Kernel γ β, IsMarkovKernel κ ∧ K =ᵐ[μ] κ ∘ₖ L

/-- Factoring everywhere implies factoring almost everywhere, for every measure. -/
lemma FactorsThrough.factorsThroughAE (μ : Measure α) {K : Kernel α β} {L : Kernel α γ}
    (h : FactorsThrough K L) : FactorsThroughAE μ K L := by
  obtain ⟨κ, hκ, rfl⟩ := h
  exact ⟨κ, hκ, Filter.Eventually.of_forall fun _ => rfl⟩

/-- Every kernel factors through itself almost everywhere. -/
lemma factorsThroughAE_refl (μ : Measure α) (K : Kernel α β) : FactorsThroughAE μ K K :=
  (factorsThrough_refl K).factorsThroughAE μ

/-- Factoring almost everywhere is transitive. -/
lemma factorsThroughAE_trans (μ : Measure α) {K : Kernel α β} {L : Kernel α γ}
    {M : Kernel α δ} (hKL : FactorsThroughAE μ K L)
    (hLM : FactorsThroughAE μ L M) : FactorsThroughAE μ K M := by
  obtain ⟨κ, hκ, hKL⟩ := hKL
  obtain ⟨η, hη, hLM⟩ := hLM
  refine ⟨κ ∘ₖ η, inferInstance, ?_⟩
  filter_upwards [hKL, hLM] with x hxK hxL
  rw [hxK, Kernel.comp_apply, hxL, ← Kernel.comp_apply, Kernel.comp_assoc]

/-! ## D. Mutual factorization almost everywhere -/

/-- Two kernels factor through each other almost everywhere. -/
def MutuallyFactorAE (μ : Measure α) (K : Kernel α β) (L : Kernel α γ) : Prop :=
  FactorsThroughAE μ K L ∧ FactorsThroughAE μ L K

/-- Mutual factoring almost everywhere is reflexive. -/
lemma mutuallyFactorAE_refl (μ : Measure α) (K : Kernel α β) :
    MutuallyFactorAE μ K K :=
  ⟨factorsThroughAE_refl μ K, factorsThroughAE_refl μ K⟩

/-- Mutual factoring almost everywhere is symmetric. -/
lemma mutuallyFactorAE_symm (μ : Measure α) {K : Kernel α β} {L : Kernel α γ}
    (h : MutuallyFactorAE μ K L) : MutuallyFactorAE μ L K :=
  h.symm

/-- Mutual factoring almost everywhere is transitive. -/
lemma mutuallyFactorAE_trans (μ : Measure α) {K : Kernel α β} {L : Kernel α γ}
    {M : Kernel α δ} (hKL : MutuallyFactorAE μ K L)
    (hLM : MutuallyFactorAE μ L M) : MutuallyFactorAE μ K M :=
  ⟨factorsThroughAE_trans μ hKL.1 hLM.1, factorsThroughAE_trans μ hLM.2 hKL.2⟩

/-- Kernels equal almost everywhere factor through each other almost everywhere. -/
lemma mutuallyFactorAE_of_ae_eq (μ : Measure α) {K L : Kernel α β} (h : K =ᵐ[μ] L) :
    MutuallyFactorAE μ K L := by
  refine ⟨⟨Kernel.id, inferInstance, ?_⟩, ⟨Kernel.id, inferInstance, ?_⟩⟩
  · filter_upwards [h] with x hx
    simpa using hx
  · filter_upwards [h.symm] with x hx
    simpa using hx

/-! ## E. Kernels equal almost everywhere -/

/-- On a countably generated outcome space, two finite kernels which, for each event, give it the
same measure at almost every input, are equal at almost every input. -/
lemma ae_eq_of_forall_ae_apply_eq [MeasurableSpace.CountablyGenerated β] {μ : Measure α}
    {K L : Kernel α β} [IsFiniteKernel K]
    (h : ∀ s, MeasurableSet s → ∀ᵐ x ∂μ, K x s = L x s) : K =ᵐ[μ] L := by
  let π : Set (Set β) :=
    Set.range fun F : Finset ℕ => ⋂ n ∈ F, MeasurableSpace.natGeneratingSequence β n
  have hmeas : ∀ t ∈ π, MeasurableSet t := by
    rintro _ ⟨F, rfl⟩
    exact .biInter F.countable_toSet fun n _ =>
      MeasurableSpace.measurableSet_natGeneratingSequence n
  have hπ : IsPiSystem π := by
    rintro _ ⟨F, rfl⟩ _ ⟨G, rfl⟩ -
    exact ⟨F ∪ G, by ext; simp [or_imp, forall_and]⟩
  have hgen : ‹MeasurableSpace β› = .generateFrom π := by
    refine le_antisymm ?_ (MeasurableSpace.generateFrom_le hmeas)
    rw [← MeasurableSpace.generateFrom_natGeneratingSequence β]
    refine MeasurableSpace.generateFrom_mono ?_
    rintro _ ⟨n, rfl⟩
    exact ⟨{n}, by simp⟩
  filter_upwards [(ae_ball_iff (Set.countable_range _)).2 fun t ht => h t (hmeas t ht),
    h .univ .univ] with x hx huniv
  exact ext_of_generate_finite π hgen hπ hx huniv

end Factorization

/-! ## F. Common refinements -/

section Refinement

variable {α : Type u} [MeasurableSpace α] {β γ δ ε : Type v} [MeasurableSpace β]
  [MeasurableSpace γ] [MeasurableSpace δ] [MeasurableSpace ε]

/-- Two kernels have a common refinement: both factor through one kernel `G`. -/
def HaveCommonRefinement (K : Kernel α β) (L : Kernel α γ) : Prop :=
  ∃ (Ω : Type v) (_ : MeasurableSpace Ω) (G : Kernel α Ω), FactorsThrough K G ∧ FactorsThrough L G

/-- Every kernel is a common refinement of itself and itself. -/
lemma haveCommonRefinement_refl (K : Kernel α β) : HaveCommonRefinement K K :=
  ⟨β, inferInstance, K, factorsThrough_refl K, factorsThrough_refl K⟩

/-- Having a common refinement is symmetric. -/
lemma haveCommonRefinement_symm {K : Kernel α β} {L : Kernel α γ}
    (h : HaveCommonRefinement K L) : HaveCommonRefinement L K := by
  obtain ⟨Ω, mΩ, G, hK, hL⟩ := h
  exact ⟨Ω, mΩ, G, hL, hK⟩

/-- A common refinement of `K` and `L` refines everything that factors through them. -/
lemma HaveCommonRefinement.mono {K : Kernel α β} {L : Kernel α γ}
    {K' : Kernel α δ} {L' : Kernel α ε} (h : HaveCommonRefinement K L)
    (hK : FactorsThrough K' K) (hL : FactorsThrough L' L) : HaveCommonRefinement K' L' := by
  obtain ⟨Ω, mΩ, G, hKG, hLG⟩ := h
  exact ⟨Ω, mΩ, G, factorsThrough_trans hK hKG, factorsThrough_trans hL hLG⟩

/-- If `K` factors through `L`, then `L` is a common refinement of both. -/
lemma haveCommonRefinement_of_factorsThrough_left {K : Kernel α β} {L : Kernel α γ}
    (h : FactorsThrough K L) : HaveCommonRefinement K L :=
  ⟨γ, inferInstance, L, h, factorsThrough_refl L⟩

/-- If `L` factors through `K`, then `K` is a common refinement of both. -/
lemma haveCommonRefinement_of_factorsThrough_right {K : Kernel α β} {L : Kernel α γ}
    (h : FactorsThrough L K) : HaveCommonRefinement K L :=
  haveCommonRefinement_symm (haveCommonRefinement_of_factorsThrough_left h)

end Refinement

end ProbabilityTheory.Kernel
