/-
Copyright (c) 2026 Michal Mogielnicki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Mogielnicki
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Real analysis lemmas

Open sets, intervals and reparametrisations of `ℝ`.

## i. Overview

Used to localise variational arguments to a window of time.

## ii. Key results

- `exists_Icc_subset`
- `eqOn_Icc_of_eqOn_Ioo`
- `exists_reparam`

## iii. Table of contents

- A. Intervals
- B. Reparametrisations

## iv. References

* None.
-/

@[expose] public section

open Set
open scoped ContDiff

/-!
## A. Intervals
-/

/-- An open set of reals contains a closed interval around each of its points. -/
lemma exists_Icc_subset {O : Set ℝ} (hO : IsOpen O) {τ : ℝ} (hτ : τ ∈ O) :
    ∃ δ > 0, Icc (τ - δ) (τ + δ) ⊆ O := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hO τ hτ
  refine ⟨r / 2, by positivity, fun σ hσ ↦ hball ?_⟩
  rw [Metric.mem_ball, Real.dist_eq, abs_lt]
  constructor <;> linarith [hσ.1, hσ.2]

/-- A continuous function vanishing on `(0, T)` vanishes on `[0, T]`. -/
lemma eqOn_Icc_of_eqOn_Ioo {F : Type*} [NormedAddCommGroup F] {f : ℝ → F} (hf : Continuous f)
    {T : ℝ} (hT : 0 < T) (h : ∀ τ ∈ Ioo 0 T, f τ = 0) : ∀ τ ∈ Icc 0 T, f τ = 0 := by
  have := Set.EqOn.closure (f := f) (g := fun _ ↦ 0) h hf continuous_const
  rwa [closure_Ioo hT.ne] at this

/-!
## B. Reparametrisations
-/

/-- A smooth reparametrisation of `ℝ` with values in `[-ε, ε]` and unit derivative at `0`. -/
lemma exists_reparam {ε : ℝ} (hε : 0 < ε) :
    ∃ σ : ℝ → ℝ, ContDiff ℝ ∞ σ ∧ σ 0 = 0 ∧ deriv σ 0 = 1 ∧ ∀ s, σ s ∈ Icc (-ε) ε := by
  refine ⟨fun s ↦ ε * Real.sin (s / ε), ?_, by simp, ?_, fun s ↦ ?_⟩
  · exact contDiff_const.mul (Real.contDiff_sin.comp (contDiff_id.div_const ε))
  · have : HasDerivAt (fun s : ℝ ↦ ε * Real.sin (s / ε)) (ε * (Real.cos (0 / ε) * (1 / ε))) 0 :=
      HasDerivAt.const_mul ε (HasDerivAt.sin (((hasDerivAt_id' (0 : ℝ)).div_const ε)))
    rw [this.deriv]; field_simp; simp
  · constructor
    · nlinarith [Real.neg_one_le_sin (s / ε)]
    · nlinarith [Real.sin_le_one (s / ε)]
