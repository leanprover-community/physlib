/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Tactic.Cases

/-!

# Parametric Integration

In this module we give some lemmas around parametric integration in Lean.
These extend some lemmas in Mathlib, and give them in a more physics-friendly way.

-/

@[expose] public section
noncomputable section
open Module
open scoped InnerProductSpace

variable {M N : Type}
    [NormedAddCommGroup M] [NormedSpace ℝ M] [ProperSpace M]
    [NormedAddCommGroup N] [NormedSpace ℝ N]
open MeasureTheory
lemma hasFDerivAt_parametric_intervalIntegral_of_contDiff
    {F : M → ℝ → N} (hf : ContDiff ℝ 1 ↿F) (x₀ : M) :
    HasFDerivAt (fun (x : M) => ∫ (t : ℝ) in 0..1, F x t ∂(volume))
      (∫ (t : ℝ) in 0..1, fderiv ℝ (F · t) x₀ ∂(volume)) x₀ := by
  let F' : M → ℝ → M →L[ℝ] N := fun x t => fderiv ℝ (F · t) x
  let s (x₀) : Set M := Metric.closedBall x₀ 1
  have hF' : Continuous ↿F' := by fun_prop
  obtain ⟨a, ha⟩ := IsCompact.exists_isMaxOn (s := s x₀ ×ˢ Set.Icc (0 : ℝ) (1 : ℝ))
      ((isCompact_closedBall x₀ 1).prod isCompact_Icc)
      (f := fun (a : M × ℝ) => ‖F' a.1 a.2‖)
      (by simp [s])
      (continuous_norm.comp hF').continuousOn
  have hx := hf.differentiable (by simp)
  apply intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (s := s x₀)
    (F' := F') (bound := fun t => ‖F' a.1 a.2‖)
  · exact Metric.closedBall_mem_nhds x₀ one_pos
  · filter_upwards with x
    apply Continuous.aestronglyMeasurable
    fun_prop
  · apply Continuous.intervalIntegrable
    fun_prop
  · apply Continuous.aestronglyMeasurable
    exact Continuous.uncurry_left x₀ (by fun_prop)
  · filter_upwards with t h x hx
    exact ha.2 (Set.mk_mem_prod hx (Set.Ioc_subset_Icc_self (by simpa using h)))
  · exact intervalIntegrable_const
  · filter_upwards with t h x hx
    exact DifferentiableAt.hasFDerivAt (by fun_prop)

lemma fderiv_apply_parametric_intervalIntegral
    {F : M → ℝ → N} (hf : ContDiff ℝ 1 ↿F) (x₀ : M) (v : M) :
    fderiv ℝ (fun (x : M) => ∫ (t : ℝ) in 0..1, F x t ∂(volume)) x₀ v =
      ∫ (t : ℝ) in 0..1, fderiv ℝ (F · t) x₀ v ∂(volume) := by
  rw [(hasFDerivAt_parametric_intervalIntegral_of_contDiff hf x₀).fderiv]
  refine ContinuousLinearMap.intervalIntegral_apply ?_ v
  apply Continuous.intervalIntegrable
  fun_prop

lemma fderiv_parametric_intervalIntegral
    {F : M → ℝ → N} (hf : ContDiff ℝ 1 ↿F) (x₀ : M) :
    fderiv ℝ (fun (x : M) => ∫ (t : ℝ) in 0..1, F x t ∂(volume)) =
      fun x => ∫ (t : ℝ) in 0..1, fderiv ℝ (F · t) x ∂(volume) := by
  have h := hasFDerivAt_parametric_intervalIntegral_of_contDiff hf x₀
  ext1 x
  exact (hasFDerivAt_parametric_intervalIntegral_of_contDiff hf x).fderiv

lemma contDiff_one_parametric_intervalIntegral_of_contDiff
    {F : M → ℝ → N} (hf : ContDiff ℝ 1 ↿F) :
    ContDiff ℝ 1 (fun (x : M) => ∫ (t : ℝ) in 0..1, F x t ∂(volume)) := by
  rw [contDiff_one_iff_hasFDerivAt]
  refine ⟨_, ?_, hasFDerivAt_parametric_intervalIntegral_of_contDiff hf⟩
  fun_prop

lemma contDiff_succ_parametric_intervalIntegral_of_contDiff {n : ℕ} [FiniteDimensional ℝ M]
    {F : M → ℝ → N} (hf : ContDiff ℝ (n + 1) ↿F) :
    ContDiff ℝ (n + 1) (fun (x : M) => ∫ (t : ℝ) in 0..1, F x t ∂(volume)) := by
  induction' n with n ih generalizing F
  · exact contDiff_one_parametric_intervalIntegral_of_contDiff hf
  · rw [contDiff_succ_iff_fderiv]
    refine ⟨ContDiff.differentiable
      (contDiff_one_parametric_intervalIntegral_of_contDiff (hf.of_le (by simp))) (by simp), ?_⟩
    simp only [Nat.cast_add, Nat.cast_one, WithTop.add_eq_top, WithTop.natCast_ne_top,
      WithTop.one_ne_top, or_self, IsEmpty.forall_iff, true_and, contDiff_clm_apply_iff,
      fderiv_apply_parametric_intervalIntegral (hf.of_le (by simp))]
    exact fun y => ih (by fun_prop)

lemma contDiff_parametric_intervalIntegral_of_contDiff {n : ℕ} {M : Type}
    [NormedAddCommGroup M] [NormedSpace ℝ M] [ProperSpace M] [FiniteDimensional ℝ M]
    {F : M → ℝ → N} (hf : ContDiff ℝ n ↿F) :
    ContDiff ℝ n (fun (x : M) => ∫ (t : ℝ) in 0..1, F x t ∂(volume)) := by
  induction' n with n ih generalizing F
  · exact contDiff_zero.mpr (by fun_prop)
  · exact contDiff_succ_parametric_intervalIntegral_of_contDiff (hf.of_le (by simp))

open Set in
/-- Differentiation under the integral sign for a `C¹` integrand. -/
lemma hasDerivAt_intervalIntegral_of_contDiff {F : ℝ × ℝ → N}
    (hF : ContDiff ℝ 1 F) (a b x₀ : ℝ) :
    HasDerivAt (fun x ↦ ∫ t in a..b, F (x, t))
      (∫ t in a..b, fderiv ℝ F (x₀, t) (1, 0)) x₀ := by
  have hK : IsCompact (Icc (x₀ - 1) (x₀ + 1) ×ˢ uIcc a b) := isCompact_Icc.prod isCompact_uIcc
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hF.continuous_fderiv one_ne_zero).continuousOn
  have hcont : ∀ x, Continuous fun t ↦ F (x, t) := fun x ↦ hF.continuous.comp (by fun_prop)
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun x t ↦ F (x, t)) (F' := fun x t ↦ fderiv ℝ F (x, t) (1, 0))
    (s := Icc (x₀ - 1) (x₀ + 1)) (bound := fun _ ↦ C) (Icc_mem_nhds (by linarith) (by linarith))
    (Filter.Eventually.of_forall fun x ↦ (hcont x).aestronglyMeasurable)
    ((hcont x₀).intervalIntegrable _ _) ?_ ?_ intervalIntegrable_const ?_).2
  · exact (((hF.continuous_fderiv one_ne_zero).comp (by fun_prop)).clm_apply
      continuous_const).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun t ht x hx ↦ ?_
    calc ‖fderiv ℝ F (x, t) (1, 0)‖ ≤ ‖fderiv ℝ F (x, t)‖ * ‖((1 : ℝ), (0 : ℝ))‖ :=
          (fderiv ℝ F (x, t)).le_opNorm _
      _ ≤ C := by simpa using hC (x, t) ⟨hx, uIoc_subset_uIcc ht⟩
  · exact Filter.Eventually.of_forall fun t _ x _ ↦
      (hF.differentiable one_ne_zero (x, t)).hasFDerivAt.comp_hasDerivAt x
        ((hasDerivAt_id x).prodMk (hasDerivAt_const x t))
