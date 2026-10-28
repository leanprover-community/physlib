/-
Copyright (c) 2026 Michal Mogielnicki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Mogielnicki
-/
module

public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Fundamental lemma on an interval

The fundamental lemma of variational calculus on `[a, b]`.

## i. Overview

A covector-valued `f` continuous on `[a, b]` with zero integral against every smooth `ψ`
supported in `(a, b)` vanishes. This is the step from a stationary action to the Euler-Lagrange
equations, see `LagrangianSystem.eulerLagrange_eq_zero_of_isCriticalPoint`.

## ii. Key results

- `eqOn_Icc_zero_of_integral_contDiff_smul_eq_zero`: the fundamental lemma on `[a, b]`

## iii. Table of contents

- A. The fundamental lemma

## iv. References

* V. I. Arnold, Mathematical Methods of Classical Mechanics. [ref: arnold_mechanics]
* L. D. Landau and E. M. Lifshitz, Mechanics. [ref: landau_mechanics]
-/

@[expose] public section

open Set MeasureTheory
open scoped ContDiff
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-!
## A. The fundamental lemma
-/

/-- If `f : ℝ → V →L[ℝ] ℝ` is continuous on `[a, b]` and `∫ x in a..b, f x (ψ x • v) = 0` for
every smooth `ψ` supported in `(a, b)` and every `v : V`, then `f = 0` on `[a, b]`. -/
lemma eqOn_Icc_zero_of_integral_contDiff_smul_eq_zero {f : ℝ → V →L[ℝ] ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b)) (hab : a < b)
    (hint : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → tsupport ψ ⊆ Ioo a b →
      ∀ v : V, ∫ x in a..b, f x (ψ x • v) = 0) :
    ∀ x ∈ Icc a b, f x = 0 := by
  refine EqOn.of_subset_closure (s := Ioo a b) (fun x₀ hx₀ ↦ ?_) hf
    continuousOn_const Ioo_subset_Icc_self (by rw [closure_Ioo hab.ne])
  refine ContinuousLinearMap.ext fun v ↦ ?_
  have hcv : ContinuousOn (fun x ↦ f x v) (Icc a b) := by fun_prop
  have hae := IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero isOpen_Ioo (μ := volume)
    (f := fun x ↦ f x v) ((hcv.mono Ioo_subset_Icc_self).locallyIntegrableOn measurableSet_Ioo) (by
      intro g hg hgc hgs
      have hg0 := hint g hg hgs v
      simp only [map_smul] at hg0
      rw [intervalIntegral.integral_of_le hab.le] at hg0
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioc a b)]
      · exact hg0
      · intro x hx
        have hx' : x ∉ tsupport g := fun hx' ↦ hx (Ioo_subset_Ioc_self (hgs hx'))
        simp [image_eq_zero_of_notMem_tsupport hx'])
  refine Measure.eqOn_open_of_ae_eq (μ := volume) (g := 0) ?_ isOpen_Ioo
    (hcv.mono Ioo_subset_Icc_self) continuousOn_const hx₀
  exact (ae_restrict_iff' measurableSet_Ioo).2 (hae.mono fun x hx hxU ↦ by simpa using hx hxU)
