/-
Copyright (c) 2026 Michal Mogielnicki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Mogielnicki
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Real analysis lemmas

Intervals of `ℝ` and bounded smooth functions.

## i. Overview

Used to extend identities from open to closed intervals and to localise arguments to a
subinterval.

## ii. Key results

- `IsOpen.exists_Icc_subset`
- `Continuous.eqOn_Icc_of_eqOn_Ioo`
- `exists_contDiff_mem_Icc_deriv_zero_eq_one`

## iii. Table of contents

- A. Intervals
- B. Bounded smooth functions

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
lemma IsOpen.exists_Icc_subset {O : Set ℝ} (hO : IsOpen O) {τ : ℝ} (hτ : τ ∈ O) :
    ∃ δ > 0, Icc (τ - δ) (τ + δ) ⊆ O := by
  simpa [Real.closedBall_eq_Icc] using Metric.nhds_basis_closedBall.mem_iff.1 (hO.mem_nhds hτ)

/-- Continuous functions agreeing on `(a, b)` agree on `[a, b]`. -/
lemma Continuous.eqOn_Icc_of_eqOn_Ioo {F : Type*} [TopologicalSpace F] [T2Space F]
    {f g : ℝ → F} (hf : Continuous f) (hg : Continuous g) {a b : ℝ} (hab : a < b)
    (h : ∀ τ ∈ Ioo a b, f τ = g τ) : ∀ τ ∈ Icc a b, f τ = g τ :=
  Set.EqOn.of_subset_closure h hf.continuousOn hg.continuousOn Ioo_subset_Icc_self
    (by rw [closure_Ioo hab.ne])

/-!
## B. Bounded smooth functions
-/

/-- A smooth function `σ : ℝ → ℝ` with `σ 0 = 0`, `σ' 0 = 1` and values in `[-ε, ε]`. -/
lemma exists_contDiff_mem_Icc_deriv_zero_eq_one {ε : ℝ} (hε : 0 < ε) :
    ∃ σ : ℝ → ℝ, ContDiff ℝ ∞ σ ∧ σ 0 = 0 ∧ deriv σ 0 = 1 ∧ ∀ s, σ s ∈ Icc (-ε) ε :=
  ⟨fun s ↦ ε * Real.sin (s / ε), by fun_prop, by simp, by simp; field_simp, fun s ↦ by
    constructor <;> nlinarith [Real.neg_one_le_sin (s / ε), Real.sin_le_one (s / ε)]⟩
