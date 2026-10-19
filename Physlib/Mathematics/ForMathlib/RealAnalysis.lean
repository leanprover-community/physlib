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

- `IsOpen.exists_Icc_subset`
- `Continuous.eqOn_Icc_of_eqOn_Ioo`
- `contDiffAt_comp_add_const_iff`
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
lemma IsOpen.exists_Icc_subset {O : Set ℝ} (hO : IsOpen O) {τ : ℝ} (hτ : τ ∈ O) :
    ∃ δ > 0, Icc (τ - δ) (τ + δ) ⊆ O := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hO τ hτ
  exact ⟨r / 2, by positivity,
    Real.closedBall_eq_Icc ▸ (Metric.closedBall_subset_ball (by linarith)).trans hball⟩

/-- A continuous function vanishing on `(0, T)` vanishes on `[0, T]`. -/
lemma Continuous.eqOn_Icc_of_eqOn_Ioo {F : Type*} [NormedAddCommGroup F] {f : ℝ → F}
    (hf : Continuous f) {T : ℝ} (hT : 0 < T) (h : ∀ τ ∈ Ioo 0 T, f τ = 0) :
    ∀ τ ∈ Icc 0 T, f τ = 0 :=
  closure_Ioo hT.ne ▸ Set.EqOn.closure (g := fun _ ↦ 0) h hf continuous_const

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
## B. Reparametrisations
-/

/-- A smooth reparametrisation of `ℝ` with values in `[-ε, ε]` and unit derivative at `0`. -/
lemma exists_reparam {ε : ℝ} (hε : 0 < ε) :
    ∃ σ : ℝ → ℝ, ContDiff ℝ ∞ σ ∧ σ 0 = 0 ∧ deriv σ 0 = 1 ∧ ∀ s, σ s ∈ Icc (-ε) ε :=
  ⟨fun s ↦ ε * Real.sin (s / ε), by fun_prop, by simp, by simp; field_simp, fun s ↦ by
    constructor <;> nlinarith [Real.neg_one_le_sin (s / ε), Real.sin_le_one (s / ε)]⟩
