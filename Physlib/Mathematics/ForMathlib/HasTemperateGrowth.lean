/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs
/-!

# Functions of temperate growth

This file is intended to collect useful general properties of `HasTemperateGrowth` which are not
(yet) in Mathlib.

-/
@[expose] public section

namespace Function.HasTemperateGrowth

open Finset
open scoped ContDiff

/-- The finite product of functions of temperate growth is again of temperate growth. -/
@[to_fun (attr := fun_prop)]
lemma prod {ι : Type*} {s : Finset ι} {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedCommRing F] [NormedAlgebra ℝ F] {f : ι → E → F}
    (hf : ∀ i ∈ s, HasTemperateGrowth (f i)) : HasTemperateGrowth (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact const _
  | insert j t hjt ih =>
    simp_rw [insert_eq, prod_union (disjoint_singleton_left.mpr hjt), prod_singleton]
    exact fun_mul (hf j <| mem_insert_self j t) (ih fun i h ↦ hf i <| mem_insert_of_mem h)

/-- The derivative of a function of temperate growth is again of temperate growth. -/
lemma fderiv {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : E → F} (hf : HasTemperateGrowth f) :
    HasTemperateGrowth (fderiv ℝ f) := by
  refine ⟨hf.1.fderiv_right (m := ∞) (by simp), fun n => ?_⟩
  obtain ⟨k, C, h⟩ := hf.2 (n + 1)
  exact ⟨k, C, fun x => norm_iteratedFDeriv_fderiv.le.trans (h x)⟩

/-- A polynomial evaluated on a function of temperate growth is again of temperate growth. -/
lemma polynomial_eval {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedCommRing F]
    [NormedAlgebra ℝ F] {f : E → F} (hf : HasTemperateGrowth f) (p : Polynomial F) :
    HasTemperateGrowth (fun x => p.eval (f x)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [Polynomial.eval_add]
    exact hp.add hq
  | monomial n a =>
    simp only [Polynomial.eval_monomial]
    exact (const a).mul (hf.pow n)

/-- The product of a function of temperate growth and a Schwartz map is integrable. -/
lemma integrable_mul_schwartzMap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {μ : MeasureTheory.Measure E}
    [μ.HasTemperateGrowth] {g : E → ℂ} (hg : HasTemperateGrowth g) (ψ : SchwartzMap E ℂ) :
    MeasureTheory.Integrable (fun x => g x * ψ x) μ := by
  have h := (SchwartzMap.smulLeftCLM ℂ g ψ).integrable (μ := μ)
  rw [SchwartzMap.smulLeftCLM_apply hg] at h
  simpa using h

end Function.HasTemperateGrowth
