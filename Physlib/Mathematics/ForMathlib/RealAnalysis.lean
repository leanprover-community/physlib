/-
Copyright (c) 2026 Michal Mogielnicki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Mogielnicki
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Real analysis lemmas

Open sets, intervals and bounded smooth functions of `ℝ`.

## i. Overview

Used to localise variational arguments to a window of time.

## ii. Key results

- `IsOpen.exists_Icc_subset`
- `Continuous.eqOn_Icc_of_eqOn_Ioo`
- `contDiffAt_comp_add_const_iff`
- `exists_smooth_bounded_unit_deriv`

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
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hO τ hτ
  exact ⟨r / 2, by positivity,
    Real.closedBall_eq_Icc ▸ (Metric.closedBall_subset_ball (by linarith)).trans hball⟩

/-- A continuous function vanishing on `(a, b)` vanishes on `[a, b]`. -/
lemma Continuous.eqOn_Icc_of_eqOn_Ioo {F : Type*} [NormedAddCommGroup F] {f : ℝ → F}
    (hf : Continuous f) {a b : ℝ} (hab : a < b) (h : ∀ τ ∈ Ioo a b, f τ = 0) :
    ∀ τ ∈ Icc a b, f τ = 0 :=
  Set.EqOn.of_subset_closure (s := Ioo a b) (g := fun _ ↦ 0) h hf.continuousOn
    continuousOn_const Ioo_subset_Icc_self (by rw [closure_Ioo hab.ne])

/-- Shifting the argument of a real function by a constant. -/
lemma contDiffAt_comp_add_const_iff {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : ℝ → F) (s : ℝ) (n : ℕ∞ω) :
    ContDiffAt ℝ n (fun τ ↦ g (τ + s)) 0 ↔ ContDiffAt ℝ n g s := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have h' : ContDiffAt ℝ n (fun τ ↦ g (τ + s)) ((fun τ : ℝ ↦ τ - s) s) := by simpa using h
    simpa [Function.comp_def] using
      h'.comp (f := fun τ : ℝ ↦ τ - s) s (contDiffAt_id.sub contDiffAt_const)
  · have h' : ContDiffAt ℝ n g ((fun τ : ℝ ↦ τ + s) 0) := by simpa using h
    exact h'.comp (f := fun τ : ℝ ↦ τ + s) 0 (contDiffAt_id.add contDiffAt_const)

/-!
## B. Bounded smooth functions
-/

/-- A smooth function `σ : ℝ → ℝ` with `σ 0 = 0`, `σ' 0 = 1` and values in `[-ε, ε]`. -/
lemma exists_smooth_bounded_unit_deriv {ε : ℝ} (hε : 0 < ε) :
    ∃ σ : ℝ → ℝ, ContDiff ℝ ∞ σ ∧ σ 0 = 0 ∧ deriv σ 0 = 1 ∧ ∀ s, σ s ∈ Icc (-ε) ε :=
  ⟨fun s ↦ ε * Real.sin (s / ε), by fun_prop, by simp, by simp; field_simp, fun s ↦ by
    constructor <;> nlinarith [Real.neg_one_le_sin (s / ε), Real.sin_le_one (s / ε)]⟩
