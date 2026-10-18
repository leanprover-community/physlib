/-
Copyright (c) 2026 Michal Mogielnicki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Mogielnicki
-/
module

public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Physlib.Mathematics.ForMathlib.RealAnalysis

/-!
# Variational calculus on an interval

Integration by parts and the fundamental lemma for covector-valued integrands.

## i. Overview

If `∫ f (ψ w) = 0` for all bumps `ψ` supported in an open subset of `(0, T)`, then `f` vanishes
there.

## ii. Key results

- `integral_by_parts_covector`
- `eq_zero_of_integral_smul_eq_zero`

## iii. Table of contents

- A. Integration by parts
- B. The fundamental lemma

## iv. References

* None.
-/

@[expose] public section

open Set MeasureTheory intervalIntegral Filter Topology
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-!
## A. Integration by parts
-/

/-- Integration by parts for a covector `P` paired with a vector `V`. -/
lemma integral_by_parts_covector {P : ℝ → E →L[ℝ] ℝ} {V : ℝ → E} (hP : ContDiff ℝ ∞ P)
    (hV : ContDiff ℝ ∞ V) (T : ℝ) :
    ∫ τ in (0 : ℝ)..T, (deriv P τ (V τ) + P τ (deriv V τ)) = P T (V T) - P 0 (V 0) := by
  refine integral_eq_sub_of_hasDerivAt (fun τ _ ↦
    (hP.differentiable (by simp) τ).hasDerivAt.clm_apply
      (hV.differentiable (by simp) τ).hasDerivAt) ?_
  exact (((hP.continuous_deriv (by simp)).clm_apply hV.continuous).add
    (hP.continuous.clm_apply (hV.continuous_deriv (by simp)))).intervalIntegrable _ _

/-!
## B. The fundamental lemma
-/

/-- Fundamental lemma of the calculus of variations on an open `U ⊆ (0, T)`, for covector-valued
`f`. -/
lemma eq_zero_of_integral_smul_eq_zero_of_isOpen {f : ℝ → E →L[ℝ] ℝ} (hf : Continuous f)
    {T : ℝ} {U : Set ℝ} (hU : IsOpen U) (hUT : U ⊆ Ioo 0 T)
    (h : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
      ∀ w : E, ∫ τ in (0 : ℝ)..T, f τ (ψ τ • w) = 0) :
    ∀ τ ∈ U, f τ = 0 := by
  intro τ₀ hτ₀
  have hT : 0 < T := (hUT hτ₀).1.trans (hUT hτ₀).2
  have hw : ∀ w : E, ∀ τ ∈ U, f τ w = 0 := by
    intro w
    have hcw : Continuous fun τ ↦ f τ w := hf.clm_apply continuous_const
    have hae := IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero hU (μ := volume)
      (f := fun τ ↦ f τ w) (hcw.locallyIntegrable.locallyIntegrableOn _) (by
        intro g hg hgc hgs
        have := h g hg hgc hgs w
        simp only [map_smul] at this
        rw [intervalIntegral.integral_of_le hT.le] at this
        rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioc 0 T)]
        · exact this
        · intro x hx
          have : x ∉ tsupport g := fun hx' ↦ hx (Ioo_subset_Ioc_self (hUT (hgs hx')))
          simp [image_eq_zero_of_notMem_tsupport this])
    have hopen : EqOn (fun τ ↦ f τ w) 0 U := by
      refine Measure.eqOn_open_of_ae_eq (μ := volume) ?_ hU hcw.continuousOn continuousOn_const
      rw [Filter.EventuallyEq, ae_restrict_iff' hU.measurableSet]
      filter_upwards [hae] with x hx hxU using by simpa using hx hxU
    exact fun τ hτ ↦ hopen hτ
  exact ContinuousLinearMap.ext fun w ↦ hw w τ₀ hτ₀

/-- Fundamental lemma of the calculus of variations on `[0, T]`, for covector-valued `f`. -/
lemma eq_zero_of_integral_smul_eq_zero {f : ℝ → E →L[ℝ] ℝ} (hf : Continuous f) {T : ℝ}
    (hT : 0 < T)
    (h : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ioo 0 T →
      ∀ w : E, ∫ τ in (0 : ℝ)..T, f τ (ψ τ • w) = 0) :
    ∀ τ ∈ Icc 0 T, f τ = 0 :=
  eqOn_Icc_of_eqOn_Ioo hf hT
    (eq_zero_of_integral_smul_eq_zero_of_isOpen hf isOpen_Ioo subset_rfl h)
