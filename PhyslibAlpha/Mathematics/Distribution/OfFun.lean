/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Analysis.Distribution.Support

/-!

# Distributions induced by smooth functions

The distribution of a continuous function is additive in the function. The weak derivative of the
distribution of a smooth function is the distribution of its derivative.

## i. Overview

A locally integrable function `u` defines the distribution `φ ↦ ∫ φ • u`. Continuous functions are
locally integrable. So the map `u ↦ ofFun u` is additive on continuous functions and commutes with
finite sums. Integration by parts for compactly supported test functions shows that the weak line
derivative of `ofFun u` is `ofFun` of the line derivative of a smooth `u`. A function vanishing
outside a set induces a distribution vanishing outside it.

## ii. Key results

- `Distribution.ofFun_continuous_add` : additivity on continuous functions.
- `Distribution.ofFun_finset_sum` : finite sums.
- `Distribution.lineDerivCLM_ofFun` : the weak derivative of the distribution of a smooth function.
- `Distribution.isVanishingOn_ofFun` : vanishing outside a set.

## iii. Table of contents

- A. Linearity
- B. Weak derivatives
- C. Support

## iv. References

None.

## A. Linearity

- `Distribution.ofFun_continuous_add` : additivity on continuous functions.
- `Distribution.ofFun_finset_sum` : finite sums.

## B. Weak derivatives

- `Distribution.lineDerivCLM_ofFun` : the weak derivative of the distribution of a smooth function.

## C. Support

- `Distribution.isVanishingOn_ofFun` : vanishing outside a set.
-/

@[expose] public section

noncomputable section

open scoped Distributions ContDiff
open MeasureTheory TopologicalSpace

namespace Distribution

variable {E V : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma ofFun_continuous_add {u w : E → V} (hu : Continuous u) (hw : Continuous w) :
    ofFun (⊤ : Opens E) (u + w) μ ⊤ =
      ofFun (⊤ : Opens E) u μ ⊤ +
        ofFun (⊤ : Opens E) w μ ⊤ :=
  ofFun_add (hu.locallyIntegrable.locallyIntegrableOn _)
    (hw.locallyIntegrable.locallyIntegrableOn _)

lemma ofFun_finset_sum {ι : Type*} (S : Finset ι) {g : ι → E → V}
    (hg : ∀ i, Continuous (g i)) :
    ofFun (⊤ : Opens E) (∑ i ∈ S, g i) μ ⊤ =
      ∑ i ∈ S, ofFun (⊤ : Opens E) (g i) μ ⊤ := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    have hc : Continuous (∑ i ∈ S, g i) := by
      have : (∑ i ∈ S, g i) = fun x => ∑ i ∈ S, g i x := funext fun x => Finset.sum_apply x S g
      rw [this]
      exact continuous_finsetSum _ fun i _ => hg i
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ofFun_continuous_add (hg a) hc, ih]

/-- The weak derivative of the distribution induced by a smooth function is the distribution
induced by its derivative. -/
lemma lineDerivCLM_ofFun {u : E → V} (hu : ContDiff ℝ ∞ u) (v : E) :
    lineDerivCLM (n := ⊤) (k := ⊤) v
        (ofFun (⊤ : Opens E) u μ ⊤) =
      ofFun (⊤ : Opens E) (fun x => fderiv ℝ u x v) μ ⊤ := by
  ext φ
  have hu1 : ContDiff ℝ ∞ (fun x => fderiv ℝ u x v) :=
    (hu.fderiv_right (by simp)).clm_apply contDiff_const
  have hloc : LocallyIntegrableOn u (⊤ : Opens E) μ :=
    hu.continuous.locallyIntegrable.locallyIntegrableOn _
  have hloc1 : LocallyIntegrableOn (fun x => fderiv ℝ u x v) (⊤ : Opens E) μ :=
    hu1.continuous.locallyIntegrable.locallyIntegrableOn _
  rw [lineDerivCLM_apply, ofFun_apply hloc,
    ofFun_apply hloc1]
  have hφ : ContDiff ℝ ∞ φ := φ.contDiff
  have hφc : HasCompactSupport φ := φ.hasCompactSupport
  have hdφ : ContDiff ℝ ∞ (fun x => fderiv ℝ φ x v) :=
    (hφ.fderiv_right (by simp)).clm_apply contDiff_const
  have hdφc : HasCompactSupport (fun x => fderiv ℝ φ x v) :=
    hφc.fderiv_apply (𝕜 := ℝ) v
  have hl : ∀ x, ((TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ v) φ) x =
      fderiv ℝ φ x v := fun x => by
    simp [TestFunction.lineDerivCLM_apply, (hφ.differentiable (by simp) x).lineDeriv_eq_fderiv]
  simp_rw [hl]
  have h := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (μ := μ) (v := v) (B := ContinuousLinearMap.lsmul ℝ ℝ)
    (f := φ) (f' := fun x => fderiv ℝ φ x v) (g := u) (g' := fun x => fderiv ℝ u x v)
    ?_ ?_ ?_ ?_ ?_
  · simpa using h.symm
  · exact (hdφ.continuous.smul hu.continuous).integrable_of_hasCompactSupport hdφc.smul_right
  · exact (hφ.continuous.smul hu1.continuous).integrable_of_hasCompactSupport hφc.smul_right
  · exact (hφ.continuous.smul hu.continuous).integrable_of_hasCompactSupport hφc.smul_right
  · intro x _
    exact ((hφ.differentiable (by simp) x).hasFDerivAt.hasLineDerivAt v)
  · intro x _
    exact ((hu.differentiable (by simp) x).hasFDerivAt.hasLineDerivAt v)

omit [FiniteDimensional ℝ E] [μ.IsAddHaarMeasure] in
/-- A distribution induced by a function that vanishes outside a set vanishes outside it. -/
lemma isVanishingOn_ofFun {u : E → V} {K : Set (E)}
    (hK : ∀ x, x ∉ K → u x = 0) :
    IsVanishingOn (ofFun (⊤ : Opens E) u μ ⊤) Kᶜ := by
  intro φ hφ
  by_cases hloc : LocallyIntegrableOn u (⊤ : Opens E) μ
  · rw [ofFun_apply hloc]
    have : (fun x => φ x • u x) = 0 := by
      funext x
      by_cases hx : φ x = 0
      · simp [hx]
      · have : x ∈ tsupport φ := subset_tsupport _ (Function.mem_support.2 hx)
        have hxK : x ∈ Kᶜ := hφ this
        simp [hK x hxK]
    rw [this]
    simp
  · rw [ofFun_eq_zero hloc]
    rfl

end Distribution
