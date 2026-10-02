/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.Classical.Basic
public import PhyslibAlpha.ProbabilisticTheory.Classical.SimplexStateSpace
public import PhyslibAlpha.Mathematics.Order.PositiveDual.UpperEnvelope

/-!
# Refinement of ensembles

## i. Overview

An ensemble is a recipe for preparing a state: choose one of finitely many states with given
probabilities. We write it as a finite list of weighted states, a state times a nonnegative weight.
Its total is their sum, the state it prepares. Two ensembles with the same total cannot be told
apart by any measurement.

Ensembles refine when any two ensembles with the same total have a common refinement. This is a
table of weighted states. Its rows add up to the members of the first ensemble, and its columns add
up to the members of the second. For a die it is a joint probability distribution with the two
ensembles as marginals.

Refinement is the physical content of being classical. On a simplex it follows from uniqueness:
decompose every member into pure states and cut. Conversely, refinement is all the uniqueness
lemma needs. A qubit shows the failure: the maximally mixed state is an equal mixture of spin up
and down and of spin left and right, and these two ensembles have no common refinement.

## ii. Key results

- `EnsemblesRefine E` states that ensembles refine.
- `IsClassical.ensemblesRefine` proves that ensembles refine when positive functionals form a
  lattice.
- `EnsemblesRefine.eq_of_sum_weighted_eq` proves that, when ensembles refine, a mixture of different
  pure states determines its weights.
- `EnsemblesRefine.upperEnvelope_add_le` proves that, when ensembles refine, upper envelopes are
  subadditive.
- `IsSimplexStateSpace.ensemblesRefine` proves that ensembles refine on a simplex.

## iii. Table of contents

- A. Ensembles of weighted states
- B. Refinement separates pure states
- C. Upper envelopes on refining ensembles
- D. Ensembles refine on a simplex

-/

@[expose] public section

namespace ProbabilisticTheory

open MeasureTheory PureState PositiveLinearMap
open scoped NNReal

/-!

## A. Ensembles of weighted states

-/

section OrderUnitSpace

/-- Ensembles of weighted states refine: any two finite families of weighted states with the same
total have a common refinement, weighted states `γ i j` whose rows add up to the first family and
whose columns add up to the second. -/
abbrev EnsemblesRefine (E : Type*) [OrderUnitSpace E] : Prop :=
  PositiveLinearMap.HasRefinement E

variable {E : Type*} [OrderUnitSpace E]

/-- On a lattice dual cone, ensembles of weighted states refine. -/
lemma IsClassical.ensemblesRefine (hE : IsClassical E) : EnsemblesRefine E := by
  exact hE.hasRefinement

/-- When ensembles refine, any two finite ensembles with the same total have a common refinement,
indexed by arbitrary finite types. -/
lemma EnsemblesRefine.exists_table (hE : EnsemblesRefine E) {ι κ : Type*} [Fintype ι] [Fintype κ]
    (α : ι → E →ₚ[ℝ] ℝ) (β : κ → E →ₚ[ℝ] ℝ) (h : ∑ i, α i = ∑ j, β j) :
    ∃ γ : ι → κ → E →ₚ[ℝ] ℝ, (∀ i, ∑ j, γ i j = α i) ∧ ∀ j, ∑ i, γ i j = β j :=
  PositiveLinearMap.HasRefinement.exists_table hE α β h

end OrderUnitSpace

variable {E : Type*} [ArchimedeanOrderUnitSpace E]

/-!

## B. Refinement separates pure states

-/

/-- When ensembles refine, a mixture of distinct pure states determines its weights. -/
lemma EnsemblesRefine.eq_of_sum_weighted_eq (hE : EnsemblesRefine E) {ι : Type*} [Fintype ι]
    {e : ι → 𝓢[ℝ, E]} (he : ∀ i, (e i).IsPure) (hinj : Function.Injective e) {a b : ι → ℝ≥0}
    (h : ∑ i, (e i).weighted (a i) = ∑ i, (e i).weighted (b i)) : a = b := by
  classical
  obtain ⟨γ, hr, hc⟩ := hE.exists_table _ _ h
  have hoff : ∀ i j, i ≠ j → γ i j = 0 := fun i j hij =>
    UnitalPositiveLinearMap.eq_zero_of_le_weighted (he i) (he j) (hinj.ne hij)
      (hr i ▸ le_sum (γ i) (Finset.mem_univ j)) (hc j ▸ le_sum (fun k => γ k j) (Finset.mem_univ i))
  funext i
  have ha := congrArg (· 1) (hr i)
  have hb := congrArg (· 1) (hc i)
  simp only [sum_apply, UnitalPositiveLinearMap.weighted_apply, map_one, mul_one] at ha hb
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [hoff i j (Ne.symm hj)]) (by simp)] at ha
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [hoff j i hj]) (by simp)] at hb
  exact NNReal.eq (ha.symm.trans hb)

/-!

## C. Upper envelopes on refining ensembles

-/

/-- **Choquet–Meyer**: when ensembles refine, the upper envelope is subadditive. -/
lemma EnsemblesRefine.upperEnvelope_add_le {ι : Type*} [Fintype ι] [Nonempty ι]
    (hE : EnsemblesRefine E) (s : ι → E)
    (α β : E →ₚ[ℝ] ℝ) : upperEnvelope s (α + β) ≤ upperEnvelope s α + upperEnvelope s β := by
  obtain ⟨ψ, hψ, hU⟩ := exists_sum_eq_upperEnvelope s (α + β)
  obtain ⟨γ, hr, hc⟩ := hE.exists_table ψ ![α, β] (by rwa [Fin.sum_univ_two])
  rw [← hU, Finset.sum_congr rfl fun i _ => congrArg (· (s i)) (hr i).symm]
  simp only [Fin.sum_univ_two, add_apply, Finset.sum_add_distrib]
  exact add_le_add (sum_apply_le_upperEnvelope (by simpa using hc 0))
    (sum_apply_le_upperEnvelope (by simpa using hc 1))

/-!

## D. Ensembles refine on a simplex

-/

variable (h : IsSimplexStateSpace E)
include h

/-- On a simplex, any two positive functionals have a least upper bound: integration against the
supremum of their measures. -/
lemma IsSimplexStateSpace.isClassical : IsClassical E := by
  intro α β
  obtain ⟨μα, hαf, hα, rfl⟩ := exists_toPositive_eq h α
  obtain ⟨μβ, hβf, hβ, rfl⟩ := exists_toPositive_eq h β
  have hsup : μα ⊔ μβ ≤ μα + μβ :=
    sup_le (Measure.le_add_right le_rfl) (Measure.le_add_left le_rfl)
  have : IsFiniteMeasure (μα ⊔ μβ) := isFiniteMeasure_of_le (μα + μβ) hsup
  have : (μα ⊔ μβ).Regular := Measure.Regular.of_le hsup
  refine ⟨toPositive (μα ⊔ μβ), fun χ hχ => ?_, fun θ hθ => ?_⟩
  · rcases hχ with rfl | rfl
    · exact toPositive_mono (ν := μα ⊔ μβ) le_sup_left
    · exact toPositive_mono (ν := μα ⊔ μβ) le_sup_right
  · obtain ⟨μθ, hθf, hθr, rfl⟩ := exists_toPositive_eq h θ
    have := hθr
    exact toPositive_mono (μ := μα ⊔ μβ) (sup_le (le_of_toPositive_le h (hθ (Set.mem_insert _ _)))
      (le_of_toPositive_le h (hθ (Set.mem_insert_of_mem _ rfl))))

/-- **On a simplex, ensembles refine.** -/
lemma IsSimplexStateSpace.ensemblesRefine : EnsemblesRefine E :=
  (IsSimplexStateSpace.isClassical h).ensemblesRefine

end ProbabilisticTheory
