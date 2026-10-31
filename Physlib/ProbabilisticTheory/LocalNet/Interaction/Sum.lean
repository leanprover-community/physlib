/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.ProbabilisticTheory.LocalNet.Interaction.Basic
public import Physlib.ProbabilisticTheory.Channel.Norm
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Integrating interactions over local regions

An interaction defines a local observable by integrating its terms over a region.

## i. Overview

The integral of an interaction gives an observable in each region. The choice of measure allows
both discrete sums and continuum integrals.

For nested regions, the observable in the larger region decomposes into the observable of the
smaller region and the remaining interaction terms. For two regions with disjoint sets of
supported terms, the observable decomposes into their contributions and the terms supported
in neither region.

## ii. Key results

- `Interaction.sumIn`: The integral of interaction terms in a region.
- `Interaction.norm_sumIn_le`: A norm bound for the integral.
- `Interaction.sumIn_add`, `Interaction.sumIn_smul`: Linearity of integration.
- `Interaction.sumIn_split`: Decomposition for nested regions.
- `Interaction.sumIn_disjoint`: Decomposition for regions with disjoint sets of terms.
- `Interaction.sumIn_count`, `Interaction.sumIn_count_tsum`: Discrete sums over finite or
  countable labels.

## iii. Table of contents

- A. Integration over a region
- B. Nested regions
- C. Disjoint regions
- D. Discrete interactions

## iv. References

-/

@[expose] public section

namespace ProbabilisticTheory

open MeasureTheory
open scoped ArchimedeanOrderUnitSpace

variable {R : Type*} [Preorder R] {A : R → Type*} [∀ X, ArchimedeanOrderUnitSpace (A X)]
  {N : LocalNet R A} {ι : Type*}

namespace Interaction

variable (Φ : Interaction N ι)

/-- The norm of a term cannot increase when included into another region. -/
lemma norm_termIn_le (Λ : R) (i : ι) : ‖Φ.termIn Λ i‖ ≤ ‖Φ.term i‖ := by
  by_cases h : Φ.supp i ≤ Λ
  · simpa [termIn, h] using (N.incl h).norm_apply_le (Φ.term i)
  · simp [termIn, h]

variable [MeasurableSpace ι] (μ : Measure ι)

/-! ## A. Integration over a region -/

/-- The observable in `Λ` obtained by integrating the interaction terms supported there. -/
noncomputable def sumIn (Λ : R) : A Λ := ∫ i, Φ.termIn Λ i ∂μ

/-- The norm of the integral is bounded by the integral of the norms. -/
lemma norm_sumIn_le (Λ : R) : ‖Φ.sumIn μ Λ‖ ≤ ∫ i, ‖Φ.termIn Λ i‖ ∂μ :=
  norm_integral_le_integral_norm _

/-- Integration preserves addition of interaction terms with the same supports. -/
lemma sumIn_add (s : ι → R) (t t' : ∀ i, A (s i)) {Λ : R}
    (h : Integrable ((⟨s, t⟩ : Interaction N ι).termIn Λ) μ)
    (h' : Integrable ((⟨s, t'⟩ : Interaction N ι).termIn Λ) μ) :
    (⟨s, t + t'⟩ : Interaction N ι).sumIn μ Λ =
      (⟨s, t⟩ : Interaction N ι).sumIn μ Λ + (⟨s, t'⟩ : Interaction N ι).sumIn μ Λ := by
  simp only [sumIn, termIn_add s t t' Λ]
  exact integral_add h h'

/-- Integration preserves scalar multiplication of interaction terms. -/
lemma sumIn_smul (s : ι → R) (c : ℝ) (t : ∀ i, A (s i)) (Λ : R) :
    (⟨s, c • t⟩ : Interaction N ι).sumIn μ Λ =
      c • (⟨s, t⟩ : Interaction N ι).sumIn μ Λ := by
  simp only [sumIn, termIn_smul s c t Λ]
  exact integral_smul c _

section Complete

variable [∀ X, CompleteSpace (A X)]

/-- Integrating the terms supported in `Λ` in a larger region `Λ'` agrees with including
the integral over `Λ` into `Λ'`. -/
lemma setIntegral_labelsIn {Λ Λ' : R} (h : Λ ≤ Λ') (hS : MeasurableSet (Φ.labelsIn Λ))
    (h1 : Integrable (Φ.termIn Λ) μ) :
    ∫ i in Φ.labelsIn Λ, Φ.termIn Λ' i ∂μ = N.incl h (Φ.sumIn μ Λ) := by
  have e := (N.incl h).toContinuousLinearMap.integral_comp_comm h1
  simp only [UnitalPositiveLinearMap.toContinuousLinearMap_apply, Φ.incl_termIn h] at e
  rwa [integral_indicator hS] at e

/-! ## B. Nested regions -/

/-- The contribution in `Λ'` from terms not supported in `Λ`. -/
noncomputable def coupling (Λ Λ' : R) : A Λ' :=
  ∫ i in (Φ.labelsIn Λ)ᶜ, Φ.termIn Λ' i ∂μ

/-- The observable in a larger region is the included observable of the smaller region
plus the remaining interaction terms. -/
lemma sumIn_split {Λ Λ' : R} (h : Λ ≤ Λ') (hS : MeasurableSet (Φ.labelsIn Λ))
    (h1 : Integrable (Φ.termIn Λ) μ) (h2 : Integrable (Φ.termIn Λ') μ) :
    Φ.sumIn μ Λ' = N.incl h (Φ.sumIn μ Λ) + Φ.coupling μ Λ Λ' := by
  rw [← Φ.setIntegral_labelsIn μ h hS h1, coupling, integral_add_compl hS h2]
  rfl

/-! ## C. Disjoint regions -/

/-- The contribution in `Λ` from terms supported in neither `Λ₁` nor `Λ₂`. -/
noncomputable def crossingIn (Λ₁ Λ₂ Λ : R) : A Λ :=
  ∫ i in (Φ.labelsIn Λ₁ ∪ Φ.labelsIn Λ₂)ᶜ, Φ.termIn Λ i ∂μ

/-- For regions with disjoint sets of supported terms, the observable in a common larger
region is the sum of their included observables and the remaining interaction terms. -/
lemma sumIn_disjoint {Λ₁ Λ₂ Λ : R} (h₁ : Λ₁ ≤ Λ) (h₂ : Λ₂ ≤ Λ)
    (hd : Disjoint (Φ.labelsIn Λ₁) (Φ.labelsIn Λ₂)) (m₁ : MeasurableSet (Φ.labelsIn Λ₁))
    (m₂ : MeasurableSet (Φ.labelsIn Λ₂)) (g₁ : Integrable (Φ.termIn Λ₁) μ)
    (g₂ : Integrable (Φ.termIn Λ₂) μ) (g : Integrable (Φ.termIn Λ) μ) :
    Φ.sumIn μ Λ = N.incl h₁ (Φ.sumIn μ Λ₁) + N.incl h₂ (Φ.sumIn μ Λ₂) +
      Φ.crossingIn μ Λ₁ Λ₂ Λ := by
  rw [← Φ.setIntegral_labelsIn μ h₁ m₁ g₁, ← Φ.setIntegral_labelsIn μ h₂ m₂ g₂,
    crossingIn, ← setIntegral_union hd m₂ g.integrableOn g.integrableOn,
    integral_add_compl (m₁.union m₂) g]
  rfl

/-! ## D. Discrete interactions -/

variable [MeasurableSingletonClass ι]

/-- With finitely many labels, integration against the counting measure is a finite sum. -/
lemma sumIn_count [Fintype ι] (Λ : R) :
    Φ.sumIn Measure.count Λ = ∑ i, Φ.termIn Λ i := by
  simp [sumIn]

/-- With countably many labels, integration against the counting measure is an infinite sum,
provided the terms are integrable. -/
lemma sumIn_count_tsum [Countable ι] {Λ : R}
    (h : Integrable (Φ.termIn Λ) Measure.count) :
    Φ.sumIn Measure.count Λ = ∑' i, Φ.termIn Λ i := by
  simp [sumIn, integral_countable h]

end Complete

end Interaction

end ProbabilisticTheory
