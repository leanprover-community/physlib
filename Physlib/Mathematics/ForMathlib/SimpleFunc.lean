/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.Function.SimpleFunc

/-!
# Real simple approximations

A nonnegative measurable real function is the increasing limit of simple functions. Every simple
function is a finite combination of indicators of its level sets.

## i. Overview

Mathlib approximates a measurable function into `ℝ≥0∞` from below by the simple functions
`SimpleFunc.eapprox`. Taking real parts gives increasing real simple functions converging
pointwise to a nonnegative measurable real function. A real simple function takes finitely many
values, so it is the sum over its values of the value times the indicator of its level set.

## ii. Key results

- `MeasureTheory.SimpleFunc.realApprox` : increasing real simple approximations.
- `MeasureTheory.SimpleFunc.tendsto_realApprox` : they converge to the function.
- `MeasureTheory.SimpleFunc.sum_range_mul_indicator` : a simple function is a finite
  combination of indicators of its level sets.

## iii. Table of contents

- A. Increasing approximations
- B. Level sets

## iv. References

-/

@[expose] public section

open Filter Topology

namespace MeasureTheory.SimpleFunc

variable {α : Type*} [MeasurableSpace α]

/-! ## A. Increasing approximations -/

/-- The increasing real simple approximations of a function, the real parts of `eapprox`. -/
noncomputable def realApprox (f : α → ℝ) (n : ℕ) : SimpleFunc α ℝ :=
  (eapprox (ENNReal.ofReal ∘ f) n).map ENNReal.toReal

lemma monotone_realApprox (f : α → ℝ) : Monotone (realApprox f) := fun _ n hmn x ↦
  ENNReal.toReal_mono (eapprox_lt_top _ n x).ne (monotone_eapprox _ hmn x)

/-- The real simple approximations of a nonnegative measurable function converge to it. -/
lemma tendsto_realApprox {f : α → ℝ} (hf : Measurable f) {x : α} (h0 : 0 ≤ f x) :
    Tendsto (realApprox f · x) atTop (𝓝 (f x)) := by
  simpa [realApprox, Function.comp_def, ENNReal.toReal_ofReal h0] using
    (ENNReal.continuousAt_toReal ENNReal.ofReal_ne_top).tendsto.comp
      (tendsto_eapprox hf.ennreal_ofReal x)

/-! ## B. Level sets -/

/-- A simple function is the sum over its values of the value times the indicator of its level
set. -/
lemma sum_range_mul_indicator (f : SimpleFunc α ℝ) (x : α) :
    ∑ y ∈ f.range, y * (f ⁻¹' {y}).indicator 1 x = f x := by
  rw [Finset.sum_eq_single_of_mem (f x) (f.mem_range_self x) fun y _ hy ↦ by
    simp [Set.indicator_of_notMem (show x ∉ f ⁻¹' {y} from hy.symm)]]
  simp

end MeasureTheory.SimpleFunc
