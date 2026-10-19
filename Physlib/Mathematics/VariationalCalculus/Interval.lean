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

The fundamental lemma for covector-valued integrands and differentiation of integrals.

## i. Overview

If `∫ f (ψ w) = 0` for all bumps `ψ` supported in an open subset of `(0, T)`, then `f` vanishes
there.

## ii. Key results

- `continuous_deriv_clm_apply_add`
- `eq_zero_of_integral_smul_eq_zero_of_isOpen`
- `eq_zero_of_integral_smul_eq_zero`
- `hasDerivAt_intervalIntegral_of_sub_indep`

## iii. Table of contents

- A. The Leibniz expression
- B. The fundamental lemma
- C. Differentiating integrals

## iv. References

* None.
-/

@[expose] public section

open Set MeasureTheory intervalIntegral
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-!
## A. The Leibniz expression
-/

/-- The Leibniz expression for a covector `P` paired with a vector `V` is continuous. -/
lemma continuous_deriv_clm_apply_add {P : ℝ → E →L[ℝ] ℝ} {V : ℝ → E} (hP : ContDiff ℝ 1 P)
    (hV : ContDiff ℝ 1 V) : Continuous fun τ ↦ deriv P τ (V τ) + P τ (deriv V τ) :=
  ((hP.continuous_deriv le_rfl).clm_apply hV.continuous).add
    (hP.continuous.clm_apply (hV.continuous_deriv le_rfl))

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
  refine ContinuousLinearMap.ext fun w ↦ ?_
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
  refine Measure.eqOn_open_of_ae_eq (μ := volume) (g := 0) ?_ hU hcw.continuousOn
    continuousOn_const hτ₀
  exact (ae_restrict_iff' hU.measurableSet).2 (hae.mono fun x hx hxU ↦ by simpa using hx hxU)

/-- Fundamental lemma of the calculus of variations on `[0, T]`, for covector-valued `f`. -/
lemma eq_zero_of_integral_smul_eq_zero {f : ℝ → E →L[ℝ] ℝ} (hf : Continuous f) {T : ℝ}
    (hT : 0 < T)
    (h : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ioo 0 T →
      ∀ w : E, ∫ τ in (0 : ℝ)..T, f τ (ψ τ • w) = 0) :
    ∀ τ ∈ Icc 0 T, f τ = 0 :=
  hf.eqOn_Icc_of_eqOn_Ioo hT
    (eq_zero_of_integral_smul_eq_zero_of_isOpen hf isOpen_Ioo subset_rfl h)

/-!
## C. Differentiating integrals
-/

/-- If two continuous integrands differ by an `s`-independent function, their integrals over
`[a, b]` have the same `s`-derivative. -/
lemma hasDerivAt_intervalIntegral_of_sub_indep {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {G Gh : ℝ → ℝ → F} {a b x : ℝ} {f' : F} (hG : ∀ s, Continuous (G s))
    (hGh : ∀ s, Continuous (Gh s)) (hkey : ∀ s τ, G s τ - Gh s τ = G 0 τ - Gh 0 τ)
    (hd : HasDerivAt (fun s ↦ ∫ τ in a..b, Gh s τ) f' x) :
    HasDerivAt (fun s ↦ ∫ τ in a..b, G s τ) f' x := by
  have hA : ∀ s, ∫ τ in a..b, G s τ =
      (∫ τ in a..b, Gh s τ) + ∫ τ in a..b, (G 0 τ - Gh 0 τ) := fun s ↦ by
    rw [← integral_add (f := Gh s) (g := fun τ ↦ G 0 τ - Gh 0 τ)
      ((hGh s).intervalIntegrable _ _) (((hG 0).sub (hGh 0)).intervalIntegrable _ _)]
    exact integral_congr fun τ _ ↦ by simp only [← hkey s τ, add_sub_cancel]
  rw [show (fun s ↦ ∫ τ in a..b, G s τ) = _ from funext hA]
  exact hd.add_const _
